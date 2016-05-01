module hamtd;

import core.cpuid:hasPopcnt;
import core.bitop:popcnt;
import std.variant;
import std.traits;
import std.meta;
import std.experimental.allocator;
import std.experimental.allocator.mallocator:Mallocator;
import std.experimental.allocator.building_blocks.scoped_allocator:ScopedAllocator;
import std.exception;
import core.exception:RangeError;
import std.bitmanip:BitArray;


/**
  References:
    - Ideal Hash Trees by Phil Bagwell - http://lampwww.epfl.ch/papers/idealhashtrees.pdf
    - Implementation in C++: https://github.com/chaelim/HAMT/
 */


/** 
  Aux implementation of popcnt.
  TODO -- Compare perf with Dlang's sw popcnt.  
 */
uint getBitCountManual(uint v) {
  v = v - ((v >> 1) & 0x55555555);                    // reuse input as temporary
  v = (v & 0x33333333) + ((v >> 2) & 0x33333333);     // temp
  return ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24; // count
}

uint getBitCountPopcnt( uint v ){
  // TODO  -- Determine which popcnt is the HW instruction.
  return popcnt( v );
}

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
{ alias HAMT32 = HAMT!(uint,Args); }


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
      rehash -- will be a no-op. HAMT's utilize an optimal strategy for organizing nodes.
      byKey
      byValue
      byKeyValue
      get(Key,lazy defaultValue)
  */
class HAMT(HashType, KeyType, ValueType, AllocatorType = ScopedAllocator!Mallocator) 
// TODO -- if isClass && has overridden "toHash" && overridden opequals 
{
private:
  import std.typecons:Tuple;
  alias KVPair        = Tuple!(KeyType,"key",ValueType,"value");
  alias HAMTType      = HAMT!(HashType,KeyType,ValueType,AllocatorType);
  alias KVPairOrHAMT  = VariantN!(KVPair.sizeof,HAMTType*,KVPair);
  
  // TODO -- Create POD quantity type for bits?
  // TODO -- Perhaps paramaterize subhashsize?
  enum  SubHashSize = 5; // In bits
  enum  SubHashMask = (1 << SubHashSize) - 1;
  
  // SubHashesPerHash is used to determine when to rehash the key, i.e. when the limit of unique chunks of the hash has been met. 
  enum  SubHashesPerHash      = HashType.sizeof / SubHashSize;
  enum  RehashThresholdDepth  = SubHashesPerHash;
  

  public:
    /**
      */
    // this( AllocatorType a )
    // {
    //   enforce(a !is null, "Allocator argument cannot be null");
    //   this(0,DefaultVarArraySize,a);
    // }
        
    /**
      If no runtime allocator arg is specified, use global instance.
      */
    this()
    {
       this(0,DefaultVarArraySize);
    }
    
  private
  {
    enum DefaultVarArraySize = 0;
    /**
      Private constructor allows initialization of depth argument to be something other than 0 (root).
      */
    this(uint depthArg, size_t varArraySize)//, AllocatorType allocArg)
    { 
      bitArray = BitArray( internalBits.sizeof, cast(size_t*)&internalBits );
      //allocator = allocArg;
      depth = depthArg;
      if (varArraySize != 0)
      {
        varArray = allocateVarArray(varArraySize);
      }
      
      
      // Set getBitCountFun method
      if( !hasPopcnt() )
      {
        getBitCountFun = &getBitCountPopcnt;
      }
      else 
      {
        getBitCountFun = &getBitCountManual;
      }
      
    }
    
    bool isRoot() pure nothrow @safe
    { return depth == 0; }
  }
  
  
  /**
    Removes and deallocates all nodes and data values from the tree.
    */
  void clear() @property 
  {
    allocator.dispose(varArray);
  }
  ~this()
  { clear(); }

  
  /**
    Returns number of elements in entire tree. 
    */
  size_t length() const nothrow pure @property
  { return count; }


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
  void each(EachDelegate d)
  {
    if (count==0)
    { return; }
    
    auto fullSlots = this.bitArray.bitsSet();
    foreach (s; fullSlots)
    {
      auto varIndex = getTablePosition(s);
      auto var = variantArray[varIndex];
      var.visit!(
        (HAMTType* hamt)=>
        {
          assert(hamt);
          hamt.each(d);
        },
        (KVPair kv)=>
        {
          d(kv.key,kv.value);
        }
      );
    }
  }


  /**
    Returns true if there are no elements in the tree. 
    */
  bool empty() pure
  out(result)
  {
    if( result )
    { 
      assert(internalBits == 0, "bitArray is not in sync with varArray");
      assert(varArray.length == 0); 
    }
  }
  body
  {
    return this.length() == 0;
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
      this.each(delegate void(const KeyType k, const ValueType v){result ~= k;});
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
      this.each(delegate void(const KeyType k, const ValueType v){result ~= v;});
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
  bool opBinaryRight(string op)(const KeyType rhs)
    if (op == "in" )
  {
    return this.find(rhs) != null;
  }
  unittest
  {
    auto a = HAMT32!(int,double);
    assert( 1 !in a );
  }
  
  
  /**
    */  
  ValueType opIndex(const KeyType key)
  {
    auto valuePtr = find(key);
    if (valuePtr == null)
    { throw new RangeError(); }
    return *valuePtr;
  }
  
  
  /**
    
    */
  void opIndexAssign(const ValueType value, const KeyType key)
  { this.insert(key,value); }
  
  
  /**
    Returns value, if found. Else, null.
    Searches tree recursively.
    */
  ValueType* find(immutable KeyType key)
  {
    if (empty())
    { return null; }
    
    // Hash the key
    immutable auto bitIndex = this.getBitArrayIndex(getHash(key));
    
    // Test bit index
    if (bitArray[bitIndex] == 0) 
    { return null; }
    
    auto varIndex = getTablePosition(bitIndex);
    assert(varArray.length > varIndex);
    
    // Switch on the type of variant.
    // If KVPair, and keys match, return the value found.
    // If HAMT, recurse and search for the key deeper in the tree.
    auto var = varArray[varIndex];
    return var.visit!
    (
      (HAMTType* hamt) =>
        { 
          assert( hamt !is null); 
          return hamt.find(key);
        },
      (KVPair kv) =>
        { 
          if (kv.key == key)
          { return kv.value; }
          return null; 
        },
      () => 
        { assert(0,"Logic error. Empty variant case should have been covered."); } )();
  }
  unittest
  {
    auto a = HAMT32!(int,string);
    assert(a.empty());
    assert(a.find(2)==null); 
  }
  
  
  
  
  /** 
    Uses allocator to create a new table of the given desired size. 
    Old table values are copied to the new table.
    The old table is disposed via the allocator.
    Throws on memory error.
    
    TODO -- Does marking the return type as "ref" help?
    */
  KVPairOrHAMT[] reallocateVarArray(ref KVPairOrHAMT[] oldTable, size_t desiredSize )
  {
    auto newTable = allocateVarArray(desiredSize);
    newTable[] = oldTable;
    allocator.dispose(oldTable);
    return newTable;
  }
  
  /**
    Throws on memory error.
    */
  KVPairOrHAMT[] allocateVarArray(size_t size)
  {
    import std.experimental.allocator:makeArray;
    KVPairOrHAMT[] newTable = makeArray!(KVPairOrHAMT,AllocatorType)(allocator,size);
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
    auto bitIndex = getBitArrayIndex(getHash(key));
    auto varIndex = getTablePosition(bitIndex);
    
    // If slot is not occupied, fill it.
    if (empty() || bitArray[bitIndex] == false)
    {
      // If the varArray size is too small, reallocate.
      if (varArray.length <= varIndex)
      {
        // In this case the varIndex will always be only one element larger
        //  than the existing array size. 
        auto newSize = varArray.length+1;
        varArray = reallocateVarArray(varArray,newSize); 
        // TODO -- More complex or abstract logic needed for reallocation
        //    * Could shrink array. Now only grows.
        //    * Optimal desired size when growing? Shrinking?
        assert (varArray.length == newSize);
      }
      
      // Insert into and mark the slot. 
      varArray[varIndex] = KVPair(key,value);
      bitArray[bitIndex] = true;
      count += 1;
    }
    else
    {
      // Slot is occupied. Collision. 
      //  Pivot on type.
      auto var = varArray[varIndex];
      var.visit!
      (
        (KVPair oldPair) =>
        {
          // If keys match, then the caller intends to replace.
          if (oldPair.key == key)
          { 
            oldPair.value = value;
            // Don't increment count on replacement.
            return; 
          }
          
          // Create a new HAMT tree node, assume size of two. Each key has 1/32 chance to collide again.
          // TODO -- Create better default word-aligned size
          HAMTType* hamt = allocator.make!HAMTType(depth+1, 2);
          enforce(hamt !is null,"Memory allocation failure");
          varArray[varIndex] = hamt;
          hamt.insert(oldPair.key, oldPair.value);
          hamt.insert(key,value);
          count++;
        },
        (HAMTType* hamt) =>
        {
          hamt.insert(key,value);
          count++;          
        }
      ); 
    }
    return;       
  }
  unittest
  {
    HAMT32!(int,string) hamt;
    hamt.insert(3,"three");
    assert(*(hamt.find(3)) == "three");
    assert(hamt.find(2) == null);
  }


  /**
    returns bool: whether an item was removed or not (if item not found)
    */
  bool remove(const KeyType key)
  {
    // Search for node
    auto bitIndex = getBitArrayIndex(key.getHash());
    auto varIndex = getTablePosition(bitIndex);
    
    if (empty() || bitArray[bitIndex] == false)
    {
      // Empty slot, no op.
      return false;
    }
    
    // Slot occupied. Switch on type
    auto var = variantArray[varIndex];
    var.visit(
      (KVPair* kv) =>
      {
        assert(kv !is null);
        
        // If key doesn't match, no-op
        if (kv.key != key)
        { return false; }
        
        allocator.dispose(kv);
        bitArray[bitIndex] = false;
        count -= 1;
        
        // TODO -- Handle case where this tree node is now empty.
        // Signal to caller to deallocate this node
        
        return true;
      },
      (HAMTType* hamt)=>
      {
        assert(hamt !is null);
        if (hamt.remove(key))
        { 
          //All node's count variables must be decremented.
          count -= 1;
          return true;
        }
        // Final failure case
        return false;
      }
    );
    assert(0, "Logic error. All remove cases have been covered");
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
  HashType getHash(inout ref KeyType key)
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
  HashType getBitArrayIndex(HashType hash)
  {      
    hash >>= (depth % RehashThresholdDepth) * SubHashSize;
    auto masked = hash & SubHashMask;
    return 1 << masked; 
  }


  /**
    Get the position of the item in the subarray, given the hash bit position into the map.
    The varArray is kept "sorted", in that it's sparsely populated, the filled slots are contiguous, and the filled slots are at the front of the varArray.
    If the hash resolves to 18, but there are only 10 items in the array, the desired item index is 10.
    If the hash resolves to 5, and there are 10 items in the array, the desired item index will be less than 10. 
    
    TODO -- Ensure method inlines.
    */
  auto getTablePosition( ulong bitIndex )
  {
    return getBitCountFun( internalBits & (bitIndex - 1));
  }
  
  
private:
  /**
    Each Node entry in the hash table is either terminal node
    (a ValueType pointer) or HAMT data structure.
    A one bit in the bit map represents a valid arc, while a zero an empty arc.
    The pointers in the table are kept in sorted order and correspond to
    the order of each one bit in the bit map.
    */
  // Array of variants
  KVPairOrHAMT[]    varArray;
  uint              internalBits = 0;
  BitArray          bitArray;
  
  uint              depth;
  size_t            count;
  AllocatorType     allocator;
  
  HashType function(HashType) getBitCountFun;
}

unittest
{
  // Simple tests
  {
    HAMT32!(int,int) hamt;
    
    assert(hamt.empty());
    
    hamt[3]=3;
    
    assert(hamt[3] == 3);
    assert((3 in hamt) == true);
    assertThrown!RangeError(hamt[2]);
    
    hamt.remove(3);
    
    assert(hamt.empty());
    assert((3 in hamt) != true );

    //Test addition after removal works.    
    hamt[3]=3;

    assert((3 in hamt) == true);
  }
  
  // Large number of elements
  {
    enum ElementMax = 99_999_999;
    HAMT32!(int,double) hamt;
    foreach(i;0..ElementMax)
    {
      hamt[i]=cast(double)i;
    }
    
    foreach(i;0..ElementMax)
    {
      import std.stdio:write;
      char[] msg;
      msg.write("Checking for key: ",i);
      assert( i in hamt,msg );
    }
  }
}
















