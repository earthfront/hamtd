module hamtd;

import core.cpuid : hasPopcnt;
import core.bitop : popcnt;
import std.variant;
import std.traits;
import std.meta;
// import std.experimental.allocator;
// import std.experimental.allocator.mallocator : Mallocator;
// import std.experimental.allocator.building_blocks.scoped_allocator : ScopedAllocator;
import std.exception;
import core.exception : RangeError;
import std.bitmanip : BitArray;

/**
  References:
    - Ideal Hash Trees by Phil Bagwell - http://lampwww.epfl.ch/papers/idealhashtrees.pdf
    - Implementation in C++: https://github.com/chaelim/HAMT/
 */

/**
    Workaround for allocators lack of access to data members.
  */
// T make(T, Alloc, A...)(auto ref Alloc al, A a)
//         if (is(T == class) && !isAbstractClass!T)
// {
//     auto size = typeid(T).init.length;
//     auto memory = al.allocate(size);
//     memory[0 .. size] = typeid(T).init[];
//     T result = cast(T)(memory.ptr);
//     static if (__traits(hasMember, T, "__ctor"))
//     {
//         result.__ctor(a);
//     }
//     return cast(T) memory.ptr;
// }

/** 
  Aux implementation of popcnt.
  TODO -- Compare perf with Dlang's sw popcnt.  
 */
// uint getBitCountManual(immutable uint v) pure {
//   v = v - ((v >> 1) & 0x55555555);                    // reuse input as temporary
//   v = (v & 0x33333333) + ((v >> 2) & 0x33333333);     // temp
//   return ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24; // count
// }

// uint getBitCountPopcnt( immutable uint v ) pure {
//   return popcnt( v );

// static this()
// { 

//   if( !hasPopcnt() )
//   {
//     alias getBitCountFun = getBitCountPopcnt;
//   }
//   else 
//   {
//     alias getBitCountFun = getBitCountManual;
//   }
// }

/**
  CTFE function to generate types specific to the HAMT type.
  Accepts either 16, 32 bit or 64 bit types. DRY.
  TODO -- Flesh out....
  */
/*
string createHAMTType( uint numBits, string aliasName )
{ 
  auto newName = aliasName~"32";
  return "template "~aliasName~"(Args...)
  { alias "~aliasName~" = "~structName~"!(uint,Args); }";
}
*/

/**
  Convenience aliases
  */
template HAMT32(Args...)
{
    alias HAMT32 = HAMT!(uint, Args);
}
//alias HAMT32(Args...) = HAMT!(uint,Args);

/**
  HAMT type.
  * Size of the hash type determines:
    * Length of the ValueType list and lookup table.
    * Depth threshold at which the hash must be rehashed (at 5 bit chunks, 32 bits gives 6 chunks/levels; 64bits/6bit chunks -> 10 chunks/levels;etc).
    * Can be 32 bits now. Possible 16,32,64 bits support in future. 
  KeyType must be hashable.
  ValueType must be default constructible or a pointer type.
  
  TODO -- Create a custom allocator: retains pools of arrays of various sizes. Minimum retention size for each pool. 
  
  TODO -- Specialize for value semantics, e.g. "static if (isPointer!ValueType)"
    - Value semantics for ValueType's will remove a layer of indirection from retrieving values, but increase the size of the resulting tables.
    - Reference semantics is the opposite: smaller table sizes, but an extra layer of indirection. 
    - Test the speed of each * different bit widths for the hash type.
    TODO -- optimize:
     * Replace BitArray (unnecessarily big, needs external uint anyway)
     * Optimize for alignment
  TODO -- evaluate appropriateness of ".hashOf" versus custom hash implementation
  TODO -- add function attributes, e.g. pure, nothrow, trusted, etc.
  TODO -- Evaluate optimal use of Variant memory usage, vs pointer.

  Unimplemented methods to match D's AA:
      opIndexAssign -- See all the rules about how structs are supported. Support value semantics
      staticInitialization?
      copy constructor -- Support assumeUnique
    Properties:
      keys
      values
      -rehash- -- will be a no-op. HAMT's utilize an optimal strategy for organizing nodes.
      byKey
      byValue
      byKeyValue
      get(Key,lazy defaultValue)
  */
class HAMT(HashType, KeyType, ValueType)
//, AllocatorType = ScopedAllocator!Mallocator) // TODO -- if isClass && has overridden "toHash" && overridden opequals 
{
package:
  import std.typecons : Tuple;

  alias KVPair = Tuple!(KeyType, "key", ValueType, "value");
  alias HAMTType = typeof(this); //HAMT!(HashType,KeyType,ValueType,AllocatorType);
  version( UseVariant )
  {   alias KVPairOrHAMTPtr = VariantN!(KVPair.sizeof, HAMTType*, KVPair); }
  else
    {   alias KVPairOrHAMTPtr = VariantN!(KVPair.sizeof, HAMTType*, KVPair); }

  // TODO -- Create POD quantity type for bits? To avoid implicit bit/byte conversion errors.
  // TODO -- Paramaterize subhashsize?
  enum SubHashSize = 5; // In bits. Implies 32 bit Hash size (2^5 == 32). 
  enum SubHashMask = (1 << SubHashSize) - 1;

  // SubHashesPerHash determines when to rehash the key, i.e. when the limit of unique chunks of the hash has been met. 
  enum SubHashesPerHash = (HashType.sizeof * 8) / SubHashSize;
  enum RehashThresholdDepth = SubHashesPerHash;

public:
    this()
    {
        this(0, DefaultVarArraySize);
    }

    private
    {
        enum DefaultVarArraySize = 0;
        /**
      Private constructor allows initialization of depth argument to be something other than 0 (root).
      */
        this(uint depthArg, size_t varArraySize) //, AllocatorType allocArg)
        {
            bitArray = BitArray(internalBits.sizeof * 8, cast(size_t*)&internalBits);

            //allocator = allocArg;
            depth = depthArg;
            if (varArraySize != 0)
            {
                varArray = allocateVarArray(varArraySize);
            }

            // // Set getBitCountFun method
            // if( !hasPopcnt() )
            // {
            //   getBitCountFun = &getBitCountPopcnt;
            // }
            // else 
            // {
            //   getBitCountFun = &getBitCountManual;
            // }
            // Library call already has a check to switch between soft and hard popcnt
        }

        bool isRoot() pure nothrow @safe
        {
            return depth == 0;
        }
    }

    /**
    Removes and deallocates all nodes and data values from the tree.
    */
    void clear() @property
    {
        internalBits = 0;

        //// GC Testing
        // allocator.dispose(varArray);
        varArray.length = 0;
    }

    void doHousekeeping()
    {
        // If that was the last item, clear out the memory.
        if (count == 0)
        {
            clear();
        }
    }

    ~this()
    {
        clear();
    }

    /**
    Returns number of elements in entire tree. 
    */
    size_t length() const nothrow pure @property
    {
        return count;
    }

    /**
    Returns true if there are no elements in the tree. 
    */
    bool empty() pure
    out (result)
    {
        if (result)
        {
            assert(internalBits == 0, "bitArray is not in sync with varArray");
            // Note: varArray's length may be out of
            // sync with the count. This is OK.
        }
    }
    body
    {
        return this.length() == 0;
    }

    // The size of the memory held by all trees & values can be calculated. 
    // Perhaps this should be returned?
    // This cannot be overloaded, it seems 
    //size_t sizeof() const nothrow pure @property
    //{ return size_t.sizeof; }

    /** Helper alias for each
    */
    alias EachDelegate = void delegate(const KeyType k, const ValueType v);

    /**
    Iterate over all key value pairs.
    Descend the depth of the tree and visit each leaf node.
    Callable must accept as parameters:
      ref KeyType
      ref ValueType
    */
    void eachKV(EachDelegate func)
    {
        if (count == 0)
        {
            return;
        }

        auto fullSlots = this.bitArray.bitsSet();
        foreach (s; fullSlots)
        {
          auto varIndex = getTableItemIndex(this.internalBits, s);
            auto var = varArray[varIndex];
            var.visit!((HAMTType* hamt) { assert(hamt); hamt.eachKV(func); }, (KVPair kv) {
                func(kv.key, kv.value);
            })();
        }
    }

    /**
    Calls func over all child HAMT's, then itself. 
    */
    void eachHAMTPostOrder(alias FuncType)(auto ref FuncType func)
    {
        if (count == 0)
        {
            assert(varArray.length == 0);
            return;
        }

        auto fullSlots = this.bitArray.bitsSet();
        foreach (s; fullSlots)
        {
          auto varIndex = getTableItemIndex(this.internalBits, s);
            auto var = varArray[varIndex];
            var.tryVisit!((HAMTType* hamt) {
                assert(hamt);
                hamt.eachHAMTPostOrder(func);
            })();
        }
        func(this);
    }

    // /**
    //   TODO -- Might need to change this to a class instead of struct.
    //   */
    // HAMTType dup()
    // {
    //   auto newHamt = new HAMTType; 
    //   auto pairs = this.byKeyValue();
    //   foreach( ref p; pairs )
    //   { newHamt.insert(p.key,p.value); }
    //   return newHamt;
    // }

    /**
    */
    KeyType[] keys() @property
    {
        KeyType[] result;
        result.reserve(count);
        // auto appendKey = delegate void(const KeyType a, const ValueType b){result ~= a;};
        // this.each(appendKey);
        this.eachKV(delegate void(const KeyType k, const ValueType v) {
            result ~= k;
        });
        return result;
    }

    /**
    */
    auto values() @property
    {
        ValueType[] result;
        result.reserve(count);
        //auto appendValue = delegate void(const KeyType a, const ValueType b){result ~= b;};
        //this.each!(typeof(appendValue))(appendValue);
        //auto appendValue = delegate void(const KeyType a, const ValueType b){result ~= b;};
        this.eachKV(delegate void(const KeyType k, const ValueType v) {
            result ~= v;
        });
        return result;
    }

    /**
    static struct Range(IterableType)
    {
      @disable this();
      
      TODO -- implement popFront, etc. 
      
      
      private:
        HAMTType* currentNode; // Current node in tree.
        FILLINTYPE currentIndex;
        
    }
    
    auto byKey() @property
    {
      
    }
    
    auto byValue() @property
    {
      
    }
    
    auto byKeyValue() @property
    {
      
    }
    **/
    ////// Operator overloadss
    /**
    "in" operator, Membership test.
    */
    bool opBinaryRight(string op)(const KeyType rhs) if (op == "in")
    {
        return !(this.find(rhs).isNull);
    }

    unittest
    {
        auto a = new HAMT32!(int, double);
        assert(1 !in a);
    }

    /**
    */
    ValueType opIndex(const KeyType key)
    {
        auto maybeValue = find(key);
        if (maybeValue.isNull)
        {
            throw new RangeError();
        }
        return maybeValue.get();
    }

    /**
    
    */
    void opIndexAssign(const ValueType value, const KeyType key)
    {
        this.insert(key, value);
    }

    /**
    Returns value, if found. Else, null.
    Searches tree recursively.
    */
    import std.typecons : Nullable;

    Nullable!ValueType find(immutable KeyType key)
    {
        alias nv = Nullable!ValueType;
        if (empty())
        {
            return nv();
        }

        // Hash the key
        immutable auto bitIndex = this.getBitArrayIndex(depth, getHash(key));

        // Test bit index
        if (bitArray[bitIndex] == 0)
        {
            return nv();
        }

        auto varIndex = getTableItemIndex(this.internalBits, bitIndex);
        assert(varArray.length > varIndex);

        // Switch on the type of variant.
        // If KVPair, and keys match, return the value found.
        // If HAMT, recurse and search for the key deeper in the tree.
        auto var = varArray[varIndex];
        return var.visit!((HAMTType* hamt) {
            assert(hamt !is null);
            return hamt.find(key);
        }, (KVPair kv) {
            Nullable!ValueType result;
            if (kv.key == key)
            {
                result = kv.value;
            }
            return result;
        })();
    }

    unittest
    {
        auto a = new HAMT32!(int, string);
        assert(a.empty());
        assert(a.find(2) == null);
    }

    /** 
    Uses allocator to create a new table of the given desired size. 
    Old table values are copied to the new table.
    The old table is disposed via the allocator.
    Throws on memory error.
    
    TODO -- Does marking the return type as "ref" help?
    */
  KVPairOrHAMTPtr[] reallocateVarArray(KVPairOrHAMTPtr[] oldTable, size_t desiredSize)
  {
    //// Testing with the GC for now
    // auto newTable = allocateVarArray(desiredSize);
    // newTable[0..oldTable.length] = oldTable[];
    // allocator.dispose(oldTable);

    auto newTable = new KVPairOrHAMTPtr[desiredSize];
    newTable[0 .. oldTable.length] = oldTable[];

    return newTable;
  }

    /**
    Throws on memory error.
    */
    KVPairOrHAMTPtr[] allocateVarArray(size_t size)
    {
        //// GC testing
        // import std.experimental.allocator:makeArray;
        // KVPairOrHAMTPtr[] newTable = makeArray!KVPairOrHAMTPtr(allocator,size);

        auto newTable = new KVPairOrHAMTPtr[size];
        enforce(newTable !is null, "Memory allocation failure.");
        return newTable;
    }

  /** 
      Inserts $(D value) into the tree using $(D key) as the key.  
      Mem allocation of the pair and new varArray occurs as late as possible.
      Throws on memory allocation failure.
  */
  void insert(const KeyType key, const ValueType value)
  {
    auto bitIndex = getBitArrayIndex(depth, getHash(key));

    // If slot is not occupied, fill it.
    // Short circuits if the number of elements is zero. 
    // The other scenario is there exists enough memory to store the new info.
    if (empty() || bitArray[bitIndex] == false)
      {
        auto varIndex = getTableInsertIndex(this.internalBits, bitIndex);
        
        // If the varArray size is too small, reallocate.
        if (varArray.length <= count + 1)
          {
            // In this case the varIndex will always be only one element larger
            //  than the existing array size. 
            auto newSize = varArray.length + 1;
            varArray = reallocateVarArray(varArray, newSize);
            // TODO -- More complex or abstract logic needed for reallocation
            //    * Could shrink array. Now only grows.
            //    * Optimal desired size when growing? Shrinking?
            assert(varArray.length == newSize);
          }

        // Insert into and mark the slot.
        // Shift all slots greater than our index
        // (if the insertion doesn't go into last slot)
        if (varIndex != varArray.length - 1)
          {
            for (ulong i = varArray.length - 1; i > varIndex; i--)
              {
                // TODO -- Unroll
                varArray[i] = varArray[i - 1];
              }
          }

        varArray[varIndex] = KVPair(key, value);
        bitArray[bitIndex] = true;
        count += 1;
      }
    else
      {
        // Slot is occupied. Collision. 
        //  Pivot on type.
        auto varIndex = getTableItemIndex(this.internalBits, bitIndex);
        auto var = varArray[varIndex];
        var.visit!((KVPair oldPair) {
            // If keys match, then the caller intends to replace.
            if (oldPair.key == key)
              {
                oldPair.value = value;
                // Don't increment count on replacement.
                return;
              }

            // Create a new HAMT tree node, assume size of two. Each key has 1/(HASHType.sizeof(most likely 32)) chance to collide again.
            // TODO -- Create better default word-aligned size
            //          auto hamt = allocator.make!HAMTType(depth+1, 2);
            auto hamt = new HAMTType(depth + 1, 0);
            enforce(hamt !is null, "Memory allocation failure");
            varArray[varIndex] = &hamt;
            hamt.insert(oldPair.key, oldPair.value);
            hamt.insert(key, value);
            count += 1;
          },
          (HAMTType* hamt)
          {
            hamt.insert(key, value);
            count += 1;
          });
      }
    return;
  }

    unittest
    {
        auto hamt = new HAMT32!(int, string)();
        hamt.insert(3, "three");
        assert(hamt.find(3).get() == "three");
        assert(hamt.find(2).isNull);
        assert(3 in hamt);
        assertThrown!RangeError(2 in hamt);
    }

    /**
    Removes value in the tree corresponding to the given node.
    returns bool: whether an item was removed or not (if item not found)
    */
    bool remove(const KeyType key)
    {
        // Search for node
        auto bitIndex = getBitArrayIndex(depth, getHash(key));
        auto varIndex = getTableItemIndex(this.internalBits, bitIndex);

        // If there are no items, or the given slot exists and is unoccupied
        if (empty() || bitArray[bitIndex] == false)
        {
            // Empty slot, no op.
            return false;
        }

        // Slot occupied. Switch on type
        auto var = varArray[varIndex];
        return var.visit!((KVPair kv) {
            // If key doesn't match, no-op
            //  (because there'd be a HAMT node if the keys matched; see below.)
            if (kv.key != key)
            {
                return false;
            }

            // Shift the upper items down into this spot
            if( varArray.length > 1 )
            {
              import std.algorithm:copy;
              copy(varArray[varIndex+1..$], varArray[varIndex..$-1]);
            }
            // Leave as is; tune for perf later (speed vs space)
            bitArray[bitIndex] = false;
            count -= 1;

            doHousekeeping();
            return true;
        }, (HAMTType* hamt) {
            assert(hamt !is null);
            if (hamt.remove(key))
            {
                // Remove succeeded. Reclaim empty node memory.
                // if (hamt.empty())
                // {
                //   ////GC testing
                //   //allocator.dispose(hamt);          
                // }
                bitArray[bitIndex] = false;

                // All node's count variables must be decremented.
                count -= 1;

                doHousekeeping();
                return true;
            }
            // Final failure case
            return false;
        });
    }

private:
    /**
    After the depth of the tree is larger than the SubHashesPerHash, collisions must be resolved by using a different input to the hash function.
    This function achieves that by submitting as seed the depth threshold level (not the depth, i.e. threshold levels occur every "SubHashesPerHash" depth levels).
    The Ideal Hash Trees paper recommends rehashing using the depth as an input. 
    If the keys continue to produce the same hash, collisions will continue. This is bad. For this type of collision on insertion, the tree would grow indefinitely. 
    This may not be a problem. It deserves testing. 
    TODO -- Determine if hash collisions are problematic.
    TODO -- Do not recompute hash at every depth level. It's only necessary at new depth threshold levels.
    */
    HashType getHash(KType)(auto ref KType key)
    {
        return cast(HashType)(key.hashOf(depth / RehashThresholdDepth));
        // auto hash = key.hashOf();
        // immutable auto rehashSteps = depth % RehashDepthThreshold;
        // foreach( i; 0..rehashSteps )
        // { hash = hash.hashOf(); }
        // return hash;
    }

    /**
    Translates the hash to a bit pattern representing the single "on" bit (the hash).
    E.g. hash = 8 => bit position = 100000000
    E.g. hash = 0 => bit position = 00000001
    depth is used to shift the correct bits into 'view' of the mask.
    Depth beyond sizeof(uint)/SubHashSize 
    
    TODO -- Ensure method inlines.
    */
    static HashType getBitArrayIndex(uint depth, HashType hash)
    {
        hash >>= (depth % RehashThresholdDepth) * SubHashSize;
        auto masked = hash & SubHashMask;
        return masked;
    }

    unittest
    {
        assert(getBitArrayIndex(0, 1) == 1);
        assert(getBitArrayIndex(3, 1) == 0);
        assert(getBitArrayIndex(0, 0xFFFFFFFF) == 0x1F);
        assert(getBitArrayIndex(1, 0xF0000000) == 0x0);
        assert(getBitArrayIndex(2, 0xF000) == 0x1C);
    }
  

    /**
       Get the position of where to insert into the subarray, given the hash bit position in the map.

       The varArray is kept "sorted", in that it's sparsely populated, the filled slots are contiguous, and the filled slots are at the front of the varArray.
       If the hash resolves to 18, but there are only 10 items in the array, the desired item index is 10.
       If the hash resolves to 5, and there are 10 items in the array, the desired item index will be less than 10. 
    
       TODO -- Ensure method inlines, via compile time snazz.
    */
    static auto getTableInsertIndex(T)(const T internalBits, const ulong bitIndex)
    {
      return getBitCountFun(internalBits & ((size_t(1) << (bitIndex + 1)) - 1 ) );
        // The whys:
        // * internalBits & X  // This masks off all bits higher than the target
        // * 1 << X // This creates the mask based on the given bit position
        // * bitIndex + 1 // Shift one extra time to include in the mask the bit at the slot of the target
        // * () - 1 // Enable the 'and' mask ( 0b10000 -> 0b01111 )
    }
    unittest
    {
        alias HType = HAMT32!(uint, uint);
        assert(HType.getTableInsertIndex(0, 30) == 0);
        assert(HType.getTableInsertIndex(0b1111, 30) == 4);
        assert(HType.getTableInsertIndex(0b11111111111111, 30) == 14);
        assert(HType.getTableInsertIndex(0b1010101010, 30) == 5);
        assert(HType.getTableInsertIndex(0b1111100000, 4) == 0);
    }

  
    /**
       Get the position of the item in the subarray, given the hash bit position into the map.
       The given bit index must be set.
       This uses the getTableInsertIndex to do the heavy lifting.
       The item position will be one off of the insert position. Hence why the bit must be set.
    **/
    static auto getTableItemIndex(T)(const T internalBits, const ulong bitIndex)
    in
    {
        auto a = BitArray(internalBits.sizeof * 8, cast(size_t*)&internalBits);
        assert(a[bitIndex]);
    }
    body
    {
        return getTableInsertIndex(internalBits, bitIndex) - 1;
        // * () - 1 // For zero based indexing.
        // getBitCountFun uses the hamming weight (number of set bits).
        // Alone this gives a scalar; to use with an array, it must be converted into a zero based index, i.e., subtract one from it.
    }

  unittest
  {
    assert( getTableItemIndex( 0b100000, 5 ) == 0 );
    assert( getTableItemIndex( 0b101110, 5 ) == 3 );
    assert( getTableItemIndex( 0b111111, 5 ) == 5 );
    assert( getTableItemIndex( 0b010101, 2 ) == 1 );
    assert( getTableItemIndex( 0b000001, 0 ) == 0 );
  }
            

  
    /**
     Used by 'invariant'. Recursively descends tree, checking each node. 
    */
  static void checkSanity(const HAMTType hamt)
  {
    // This node
    auto numFullSlots = hamt.getBitCountFun(hamt.internalBits);
    assert(hamt.varArray.length >= numFullSlots);
      
    // Children
    auto fullSlots = hamt.bitArray.bitsSet();
    foreach (s; fullSlots)
      {
        auto varIndex = getTableItemIndex(hamt.internalBits, s);
        auto var = hamt.varArray[varIndex];
        var.tryVisit!((const HAMTType* h) { assert(h); checkSanity(*h); }, () {  })();
      }
  }
  // Turned off while debugging.
  // invariant
  // { checkSanity( this ); }

private:
    /**
    Each Node entry in the hash table is either terminal node
    (a ValueType pointer) or HAMT data structure.
    A one bit in bitArray represents a valid "arc", while a zero is an empty arc.
    The pointers in the table are kept in sorted order and correspond to
    the order of each one bit in the bit map.
    */
    /** 
    Used to store either the Node or KV pair. 
    */
    KVPairOrHAMTPtr[] varArray;

    /**
    Used to denote which "slots" are occupied.
    */
    BitArray bitArray;

    /** 
    Used as the underlying memory for BitArray. 
    */
    uint internalBits = 0;

    /**
    Current level in the tree.
    */
    uint depth;

    /** 
    Number of K/V pairs contained in this node and all children.
    */
    size_t count;

    /**
    User specified allocator
    */
  //    AllocatorType allocator;

    /**
    Implementation of popcnt, HW or otherwise. 
    */
    // HashType function(HashType) getBitCountFun;
    alias getBitCountFun = popcnt;
}

version (unittest)
{
    void main()
    {
    }

    // Simple tests
    unittest
    {
        auto hamt = new HAMT32!(int, int)(); 

        assert(hamt.empty());

        hamt[3] = 3;

        assert(hamt[3] == 3);
        assert((3 in hamt) == true);
        assertThrown!RangeError(hamt[2]);

        hamt.remove(3);

        assert(hamt.empty());
        assert((3 in hamt) != true);

        //Test addition after removal works.    
        hamt[3] = 3;

        assert((3 in hamt) == true);
    }

    // Large number of elements
    unittest
    {
        enum ElementMax = 99_999_999;
        auto hamt = new HAMT32!(int, double)();
        foreach (i; 0 .. ElementMax)
        {
            hamt[i] = cast(double) i;
        }

        foreach (i; 0 .. ElementMax)
        {
            import std.stdio : write;

            char[] msg;
            msg.write("Checking for key: ", i);
            assert(i in hamt, msg);
        }
    }
}
