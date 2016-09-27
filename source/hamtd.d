module hamtd;

import std.stdio;
import core.cpuid : hasPopcnt;
import core.bitop : popcnt, bt, bts, btr;
import std.variant;
import std.traits;
import std.meta;
import std.exception;
import core.exception : RangeError;
import std.bitmanip : BitsSet;

version(unit_threaded){ import unit_threaded; }

/**
   References:
   - Ideal Hash Trees by Phil Bagwell - http://lampwww.epfl.ch/papers/idealhashtrees.pdf
   - Implementation in C++: https://github.com/chaelim/HAMT/
*/

// Manual manage memory because we're using tagged pointers.
// Will parameterize this _when it works_. 
import std.experimental.allocator;
import std.experimental.allocator.mallocator;
import std.conv;
import core.stdc.string:memcpy,memset;

/**
   Convenience aliases
*/
template HAMT16(Args...){
    alias HAMT32 = HAMT!(ushort, 3, Args);
}

template HAMT32(Args...){
    alias HAMT32 = HAMT!(uint, 5, Args);
}

template HAMT64(Args...){
    alias HAMT32 = HAMT!(ulong, 7, Args);
}



/**
   HAMT type.
   * Size of the hash type determines:
   * Length of the ValueType list and lookup table.
   * Depth threshold at which the hash must be rehashed (at 5 bit chunks, 32 bits gives 6 chunks/levels; 64bits/6bit chunks -> 10 chunks/levels;etc).
   KeyType must be hashable.
   ValueType must be default constructible or a pointer type.
  
   TODO -- Create a custom allocator: retains pools of arrays of various sizes. Minimum retention size for each pool. 
  
   TODO -- Specialize for value semantics, e.g. "static if (isPointer!ValueType)"
   - Value semantics for ValueType's will remove a layer of indirection from retrieving values, but increase the size of the resulting tables.
   - Reference semantics is the opposite: smaller table sizes, but an extra layer of indirection. 
   - Test the speed of each * different bit widths for the hash type.
   TODO -- optimize:
   * Optimize for alignment
   TODO -- evaluate appropriateness of ".hashOf" versus custom hash implementation
   TODO -- add function attributes, e.g. pure, nothrow, trusted, etc.

   Unimplemented methods to match D's AA:
   opIndexAssign -- See all the rules about how structs are supported. Support value semantics
   staticInitialization?
   copy constructor -- Support assumeUnique
   Properties:
   byKey
   byValue
   byKeyValue
   get(Key,lazy defaultValue)
*/
struct HAMT(HashType, uint SubHashSize, KeyType, ValueType,
            AllocatorType = Mallocator, bool RuntimeAllocatorProvided = false){

    static assert( !is( KeyType == class ) ||
                   __traits( isOverrideFunction, KeyType.opEquals ),
                   "Supplied KeyType is a class. When using a class as KeyType, the "~
                   "function 'opEquals' must be overridden. The supplied KeyType "~
                   "class does not abide.");
                   

package:
    import std.typecons : Tuple;
    alias KVPair = Tuple!(KeyType, "key", ValueType, "value");
    alias HAMTType = typeof(this);
    enum DefaultVarArraySize = 0;

    // SubHashSize is in bits. 5 implies 32 bit Hash size (2^5 == 32). 
    enum SubHashMask = (1 << SubHashSize) - 1;
    enum BitsPerHash = HashType.sizeof * 8;
    
    // SubHashesPerHash determines when to rehash the key, i.e. when
    // the limit of unique chunks of the hash has been met. 
    enum SubHashesPerHash = (BitsPerHash) / SubHashSize;

    // "After how many depth levels should we rehash?"
    enum RehashThresholdDepth = SubHashesPerHash;
    
public:
    // Copied from the well written emsi-containers package.
    // http://code.dlang.org/packages/emsi_containers
    static if (RuntimeAllocatorProvided){
        /// No default construction if an allocator must be provided.
        this() @disable;

        /**
         * Use `allocator` to allocate and free nodes in the tree.
         */
        this(AllocatorType allocator)
            in{
                assert(allocator !is null, "Allocator must not be null");
            }
        body{
            this.allocator = allocator;
        }
    }

private:
    public this(uint depthArg, size_t varArraySize){
            
        depth = depthArg;
        if (varArraySize != 0)
            varArray = allocateVarArray(varArraySize);
    }

    bool isRoot() pure nothrow @safe
    { return depth == 0; }

public:
    /**
       Removes and deallocates all nodes and data values
       from the tree.
    */
    void clear() {
        bitArray = 0;
        varArray.length = 0;
    }

    /** Adds a condition to clear() **/
    void doHousekeeping()
    {
        // If that was the last item, clear out the memory.
        if (count == 0)
            clear();
    }

    /**
       Returns number of elements in entire tree. 
    */
    size_t length() const nothrow pure @property
    { return count; }

    /**
       Returns true if there are no elements in the tree. 
    */
    bool empty() pure const
        out (result)
            {
                if (result)
                    assert(bitArray == 0, "bitArray is not in sync with varArray");
                // Note: varArray's length may be out of
                // sync with the count. This is OK.
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
    
    ~this(){
        clear();
    }
    
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
    void eachKV(EachDelegate func) const
    {
        if (count == 0)
            return;

        foreach (uint i; 0 .. BitsPerHash)
            {
                // Only look at populated table slots
                if (this.bitArray.getBitAt(i) != 1)
                    continue;

                auto varIndex =
                    getTableItemIndex(this.bitArray, i);
                auto var = varArray[varIndex];
                with (KVPairPtrOrHAMTPtr)
                    {
                        if (var.isType(PtrType.HAMTPtr))
                            {
                                auto hamtPtr = var.getHamtPtr();
                                assert(hamtPtr);
                                hamtPtr.eachKV(func);
                            }
                        else
                            {
                                auto kv = var.getKVPtr();
                                assert(kv);
                                func(kv.key, kv.value);
                            }
                    }
            }
    }
    unittest{
        HAMT32!(uint, uint) hamt;
        immutable auto max = 3_000;
        foreach( i; 0..max)
            { hamt[i] = 2;}
        auto sum = 0;
        hamt.eachKV(delegate void(const uint k, const uint v)
                    { sum += v;});
        assert( sum == max * 2,
                "EachKV failed to traverse the tree properly."); 
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

        foreach (uint s; 0 .. BitsPerHash){
            if (!bitArray.getBitAt(s))
                continue;

            auto varIndex =
                getTableItemIndex(this.bitArray, s);
            auto var = varArray[varIndex];

            version (UseVariant)
                {
                    var.tryVisit!((HAMTType* hamt) {
                            assert(hamt);
                            hamt.eachHAMTPostOrder(func);
                        })();
                }
            else
                {
                    with (KVPairPtrOrHAMTPtr)
                        {
                            if (!var.isType(PtrType.HAMTPtr))
                                continue;

                            auto hamt = var.getHamtPtr();
                            assert(hamt);
                            hamt.eachHAMTPostOrder(func);
                        }
                }

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
    KeyType[] keys() @property const
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
    unittest{
        import std.conv:to;
        HAMT32!(string,uint) hamt;
        immutable max = 3_000;
        foreach(i; 0..max){ hamt[i.to!string()] = 42; }
        const keys = hamt.keys;
        foreach(i,k; keys)
            { assert( i.to!string() == k,
                      "'keys' property returned invalid result"); }
    }

    /**
     */
    auto values() @property const
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
    unittest{
        import std.algorithm:sum;
        HAMT32!(uint, uint) hamt;
        immutable max = 3_000;
        foreach(i; 0..max){ hamt[i] = 1; }
        const lv = hamt.values;
        assert( sum(lv) == max, "'values' property returned unexpected result");
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
    ////// Operator overloads
    /**
       "in" operator, Membership test.
    */
    bool opBinaryRight(string op)(const KeyType rhs) const
        if (op == "in") 
        {
            return !(this.find(rhs).isNull);
        }

    @("Test 'in' operator")
    unittest{
        const HAMT32!(int, double) a;
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

    Nullable!ValueType find(const KeyType key) const
    {
        alias nv = Nullable!ValueType;
        if (empty())
            return nv();

        // Hash the key
        immutable auto bitIndex = this.getBitArrayIndex(depth, getHash(key));

        // Test bit index
        if (!bitArray.getBitAt(bitIndex))
            return nv();

        auto varIndex = getTableItemIndex(this.bitArray, bitIndex);
        assert(varArray.length > varIndex);

        // Switch on the type of variant.
        // If KVPair, and keys match, return the value found.
        // If HAMT, recurse and search for the key deeper in the tree.
        auto var = varArray[varIndex];
        version (UseVariant)
            {
                return var.visit!((HAMTType* hamt) {
                        assert(hamt);
                        return hamt.find(key);
                    }, (KVPair kv) {
                        Nullable!ValueType result;
                        if (kv.key == key)
                            result = kv.value;

                        return result;
                    })();
            }
        else
            {
                with (KVPairPtrOrHAMTPtr)
                    {
                        if (var.isType(PtrType.HAMTPtr))
                            {
                                auto hamt = var.getHamtPtr();
                                assert(hamt);
                                return hamt.find(key);
                            }
                        else
                            {
                                auto const kv = var.getKVPtr();
                                Nullable!ValueType result;

                                if (kv.key == key)
                                    result = kv.value;

                                return result;
                            }
                    }
            }
    }

    @("Test blank slate, find should fail")
    unittest{
        HAMT32!(int, string) a;
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
    KVPairPtrOrHAMTPtr[] reallocateVarArray(KVPairPtrOrHAMTPtr[] oldTable, size_t desiredSize)
    {
        auto newTable = allocateVarArray( desiredSize );
        newTable[0 .. oldTable.length] = oldTable[];
        return newTable;
    }

    /**
       Throws on memory error.
    */
    KVPairPtrOrHAMTPtr[] allocateVarArray(size_t size)
    {
        auto newTable = allocator.makeArray!KVPairPtrOrHAMTPtr(size);
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
        if (empty() || bitArray.getBitAt(bitIndex) == false)
            {
                auto varIndex = getTableInsertIndex(this.bitArray, bitIndex);

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

                varArray[varIndex] = allocator.make!KVPair(key, value);
                bitArray.setBitAt(bitIndex, true);
                count += 1;
            }
        else
            {
                // Slot is occupied. Collision. 
                //  Pivot on type.
                auto varIndex = getTableItemIndex(this.bitArray, bitIndex);
                auto var = varArray[varIndex];
                version (UseVariant){
                    var.visit!((KVPair oldPair) {
                            // If keys match, then the caller intends to replace.
                            if (oldPair.key == key){
                                oldPair.value = value;
                                // Don't increment count on replacement.
                                return;
                            }
                            
                            // Create a new HAMT tree node, assume size of two. Each key has 1/(HASHType.sizeof(most likely 32)) chance to collide again.
                            // TODO -- Create better default word-aligned size
                            //          auto hamt = allocator.make!HAMTType(depth+1, 2);
                            auto hamt = allocator.make!HAMTType(depth + 1, 0);
                            enforce(hamt !is null, "Memory allocation failure");
                            varArray[varIndex] = &hamt;
                            hamt.insert(oldPair.key, oldPair.value);
                            hamt.insert(key, value);
                            count += 1;
                        }, (HAMTType* hamt) { hamt.insert(key, value); count += 1; });
                }
                else
                    {
                        alias PtrType = KVPairPtrOrHAMTPtr.PtrType;
                        if (var.isType(PtrType.KVPtr))
                            {
                                auto oldPair = var.getKVPtr();
                                assert(oldPair);
                                
                                if (oldPair.key == key)
                                    {
                                        oldPair.value = value;
                                        // Don't increment count on replacement.
                                        return;
                                    }
                                
                                // Create a new HAMT tree node, assume size of two. Each key has 1/(HASHType.sizeof(most likely 32)) chance to collide again.
                                // TODO -- Create better default word-aligned size
                                //          auto hamt = allocator.make!HAMTType(depth+1, 2);
                                auto hamt = allocator.make!HAMTType(depth + 1, 0);
                                enforce(hamt !is null, "Memory allocation failure");
                                varArray[varIndex] = hamt;
                                hamt.insert(oldPair.key, oldPair.value);
                                hamt.insert(key, value);
                                count += 1;
                            }
                        else
                            {
                                auto hamt = var.getHamtPtr();
                                assert(hamt);
                                hamt.insert(key, value);
                                count += 1;
                            }

                    }
            }
        return;
    }

    @("Test insert and find, not in range")
    unittest{
        HAMT32!(int, string) hamt;
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
        auto varIndex = getTableItemIndex(this.bitArray, bitIndex);

        // If there are no items, or the given slot exists and is unoccupied
        if (empty() || bitArray.getBitAt(bitIndex) == false)
            {
                // Empty slot, no op.
                return false;
            }

        // Slot occupied. Switch on type
        auto var = varArray[varIndex];
        version (UseVariant)
            {
                return var.visit!((KVPair kv) {
                        // If key doesn't match, no-op
                        //  (because there'd be a HAMT node if the keys matched; see below.)
                        if (kv.key != key)
                            {
                                return false;
                            }

                        // Shift the upper items down into this spot
                        if (varArray.length > 1)
                            {
                                import std.algorithm : copy;

                                copy(varArray[varIndex + 1 .. $], varArray[varIndex .. $ - 1]);
                            }
                        // Leave as is; tune for perf later (speed vs space)
                        bitArray.setBitAt(bitIndex, false);
                        count -= 1;

                        doHousekeeping();
                        return true;
                    }, (HAMTType* hamt) {
                        assert(hamt);
                        if (hamt.remove(key))
                            {
                                // Remove succeeded. Reclaim empty node memory.
                                if (hamt.empty())
                                    allocator.dispose(hamt);          

                                bitArray.setBitAt(bitIndex, false);

                                // All node's count variables must be decremented.
                                count -= 1;

                                doHousekeeping();
                                return true;
                            }
                        // Final failure case
                        return false;
                    });
            }
        else
            {
                alias PtrType = KVPairPtrOrHAMTPtr.PtrType;
                if (var.isType(PtrType.KVPtr))
                    {
                        auto kv = var.getKVPtr();
                        assert(kv);
                        // If key doesn't match, no-op
                        //  (because there'd be a HAMT node if the keys matched; see below.)
                        if (kv.key != key)
                            return false;

                        // Shift the upper items down into this spot
                        if (varArray.length > 1)
                            {
                                import std.algorithm : copy;

                                copy(varArray[varIndex + 1 .. $], varArray[varIndex .. $ - 1]);
                            }

                        // Leave as is; tune for perf later (speed vs space)
                        bitArray.setBitAt(bitIndex, false);
                        count -= 1;

                        doHousekeeping();
                        return true;
                    }
                else
                    { //HAMT
                        auto hamt = var.getHamtPtr();
                        assert(hamt);
                        if (hamt.remove(key))
                            {
                                // Remove succeeded. Reclaim empty node memory.
                                if (hamt.empty())
                                    allocator.dispose(hamt);          

                                bitArray.setBitAt(bitIndex, false);

                                // All node's count variables must be decremented.
                                count -= 1;

                                doHousekeeping();
                                return true;
                            }

                        // Final failure case
                        return false;
                    }

            }

    }
    unittest{
        HAMT32!(uint, uint) hamt;
        assert( hamt.count == 0, "Empty hamt reports not empty!");
        hamt[42] = 42;
        assert( hamt.count == 1,
                "One element inserted, but count doesn't agree");
        hamt.remove(42);
        assert( hamt.count == 0,
                "Item removal did not decrement count");
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
    HashType getHash(const KeyType key)
        pure nothrow @safe const
    {
        return cast(HashType)(key.hashOf(depth / RehashThresholdDepth));
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
        pure nothrow @safe
    {
        pragma(inline);
        hash >>= (depth % RehashThresholdDepth) * SubHashSize;
        auto masked = hash & SubHashMask;
        return masked;
    }

    @("Test getBitArrayIndex function")
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
    static int getTableInsertIndex(T)(const T bitArray, const ulong bitIndex)
        pure nothrow @safe
    {
        return getBitCountFun(bitArray & ((size_t(1) << (bitIndex + 1)) - 1));
        // The whys:
        // * bitArray & X  // This masks off all bits higher than the target
        // * 1 << X // This creates the mask based on the given bit position
        // * bitIndex + 1 // Shift one extra time to include in the mask the bit at the slot of the target
        // * () - 1 // Enable the 'and' mask ( 0b10000 -> 0b01111 )
    }

    @("Test table insertion index retrieval")
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
    static int getTableItemIndex(T)(const T bitArray, const ulong bitIndex)
        in{
            import std.bitmanip : BitArray;

            auto a = BitArray(bitArray.sizeof * 8, cast(size_t*)&bitArray);
            assert(a[bitIndex]);
        }
    body{
        return getTableInsertIndex(bitArray, bitIndex) - 1;
        // * () - 1 // For zero based indexing.
        // getBitCountFun uses the hamming weight (number of set bits).
        // Alone this gives a scalar; to use with an array, it must be converted into a zero based index, i.e., subtract one from it.
    }

    @("Test table item index retrieval")
    unittest
    {
        assert(getTableItemIndex(0b100000, 5) == 0);
        assert(getTableItemIndex(0b101110, 5) == 3);
        assert(getTableItemIndex(0b111111, 5) == 5);
        assert(getTableItemIndex(0b010101, 2) == 1);
        assert(getTableItemIndex(0b000001, 0) == 0);
    }

    /**
       Used by 'invariant'. Recursively descends tree, checking each node. 
    */
    static void checkSanity( HAMTType hamt)
    {
        // This node
        auto numFullSlots = hamt.getBitCountFun(hamt.bitArray);
        assert(hamt.varArray.length >= numFullSlots);

        // Children
        foreach (uint b; 0 .. BitsPerHash)
            {
                if (hamt.bitArray.getBitAt(b))
                    {
                        auto varIndex = getTableItemIndex(hamt.bitArray, b);
                        auto var = hamt.varArray[varIndex];

                        version (UseVariant)
                            {
                                var.tryVisit!((const HAMTType* h) {
                                        assert(h);
                                        checkSanity(*h);
                                    }, () {  })();
                            }
                        else
                            {
                                alias PtrType = KVPairPtrOrHAMTPtr.PtrType;
                                if (var.isType(PtrType.HAMTPtr))
                                    {
                                        auto h = var.getHamtPtr();
                                        assert(h);
                                        checkSanity(*h);
                                    }
                            }
                    }
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
    KVPairPtrOrHAMTPtr[] varArray;

    /** 
        Denotes which virtual slots are occupied. 
    */
    HashType bitArray = 0;

    /**
       Current level in the tree.
    */
    uint depth = 0 ;

    /** 
        Number of K/V pairs contained in this node and all children.
    */
    size_t count = 0;

    /**
       User specified allocator
    */
    static if (stateSize!AllocatorType == 0)
        alias allocator = AllocatorType.instance;
    else{
        AllocatorType allocator;
    }

    /**
       Implementation of popcnt, HW or otherwise. 
    */
    // HashType function(HashType) getBitCountFun;
    alias getBitCountFun = popcnt;


    struct KVPairPtrOrHAMTPtr{
        enum PtrType{
            HAMTPtr = false,
            KVPtr = true
        }
        
    private:
        // Creates a tagged pointer using the bits of the pointer
        // guaranteed not to be used.
        import std.bitmanip : taggedPointer;
        mixin(taggedPointer!(size_t*, "kvOrHamtPtr", PtrType, "isKV", 1));
    public:
        bool isType(PtrType p) const pure nothrow 
        {return isKV == p;}
        
        void setType(PtrType t) nothrow
        {isKV = t;}
        
        KVPair* getKVPtr() inout
        {
            assert(isKV);
            return cast(KVPair*) kvOrHamtPtr;
        }
        
        HAMTType* getHamtPtr() inout
        {
            assert(!isKV);
            return cast(HAMTType*) kvOrHamtPtr;
        }
        
        void opAssign(KVPair* p) 
        {
            isKV = PtrType.KVPtr;
            kvOrHamtPtr = cast(size_t*) p;
        }
        
        void opAssign(HAMTType* p)
        {
            isKV = PtrType.HAMTPtr;
            kvOrHamtPtr = cast(size_t*) p;
        }
        
        static assert( (HAMTType*).sizeof == (size_t*).sizeof
                       && (KVPair*).sizeof == (size_t*).sizeof,
                       "ERROR! Pointer sizes don't match" );
    }
}

// bit functions
import std.traits : isUnsigned;

bool getBitAt(T)(T bits, uint index) pure nothrow if (isUnsigned!T){
    return (bits & (1 << index)) != 0;
 }

@("Test bit retrieval operation")
unittest
{
    assert(true == getBitAt(0b00010U, 1));
    assert(true == getBitAt(0b10000000000000000000U, 19));
    assert(false == getBitAt(0b0101010101U, 3));
    assert(false == getBitAt(0b11110000U, 3));
}

void setBitAt(T)(ref T bits, uint index, bool b)
    pure nothrow if (isUnsigned!T){
        if (b)
            bits |= (1 << index);
        else
            bits &= ~(1 << index);
 }

@("Test bit set function")
unittest
{
    uint x = 0b00000;
    setBitAt(x, 0, true);
    assert(x == 0b0001U);

    setBitAt(x, 1, true);
    assert(x == 0b0011U);

    setBitAt(x, 0, false);
    assert(x == 0b0010U);

    setBitAt(x, 19, true);
    assert(x == 0b10000000000000000010U);
}

version (unittest)
{
    @("Simple usage tests")
        unittest
            {
                HAMT32!(int, int) hamt;

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

    @("Test large number of elements")
        unittest
            {
                enum ElementMax = 99_999;
                HAMT32!(int, double) hamt;
                foreach (i; 0 .. ElementMax)
                        hamt[i] = cast(double) i;

                foreach (i; 0 .. ElementMax)
                        assert(i in hamt);
            }
    
    
    import std.experimental.allocator;
    import std.experimental.allocator.building_blocks.segregator:Segregator;
    import std.experimental.allocator.building_blocks.free_list : FreeList;
 
    @("Test static allocator")
        unittest{
            import std.random:uniform;
            alias AType =
                Segregator!(
                            64, FreeList!(Mallocator,0,64),
                            128, FreeList!(Mallocator,0,128),
                            256, FreeList!(Mallocator,0,256),
                            Mallocator);
            HAMT32!(uint, ulong, AType) hamt;
            
            foreach( i; 0..99_999 )
                hamt[i] = uniform(0,1_000_000);
        }
    }

