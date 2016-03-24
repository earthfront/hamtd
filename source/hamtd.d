module hamtd;

import core.cpuid:hasPopcnt;
import core.bitop:popcnt;
import std.variant;
import std.traits;
import std.experimental.allocator.mallocator:Mallocator;
import std.exception;
import std.bitmanip:BitArray;

/**
 *  References:
 *      - Ideal Hash Trees by Phil Bagwell - http://lampwww.epfl.ch/papers/idealhashtrees.pdf
 *      - Implementation in C++: https://github.com/chaelim/HAMT/
 */

/*

// Are these needed?
uint rotl32 (uint x, byte r) {
    return (x << r) | (x >> (32 - r));
}

ulong rotl64 (ulong x, byte r) {
    return (x << r) | (x >> (64 - r));
}

ulong rotr (uint x, byte r) {
    return (x >> r) | (x << (32 - r));
}

ulong rotr (ulong x, byte r) {
    return (x >> r) | (x << (64 - r));
}
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

static this(){
  
  if( !core.cpuid.hasPopcnt() )
  {
    alias getBitCount = getBitCountPopcnt;
  }
  else 
  {
    alias getBitCount = getBitCountManual;
  }
  
}

/**
  * Bit data and functions
  */
package{
    // Use the least significant bit as reference marker
    // uint   AMT_MARK_BIT    = 1;    // Using LSB for marking AMT (sub-trie) data structure
    immutable enum  HashIndexBits = 5;
    immutable enum  HashIndexMask = (1 << HashIndexBits) - 1;
    
    // Ceiling to 8 bits boundary to use all 32 bits.
    // Calculate the number of bits we can use for the successive table positions
    // Once the maximum has been reached, rehash and dive deeper :-)
    immutable enum  MaxHashBits   = ((uint.sizeof * 8 + 7) / HashIndexBits) * HashIndexBits;
    // immutable enum  MaxHAMTDepth  = MaxHashBits / HashIndexBits; // Can work past this...
    

    
}



/****************************************************************************
* Primary HashTrie type.
**/
struct HashTrie(KeyType, ValueType, AllocatorType = Mallocator) 
  if (isPointer!ValueType) 
{
  public:

    this(this) @disable;

    this( AllocatorType a ){
      enforce(a !is null,"Allocator argument cannot be null");
      allocator = a;
    }
    
    // TODO -- add index operators;
    void      add(KeyType key, ValueType value);    
    ValueType find(const ref KeyType key);    
    ValueType remove(const ref KeyType key);
    
    /** 
      *
      */
    bool empty() { return amt.empty(); }
    
    /**
      * Delete structure, but leave the items alone <- Necessary?
      */
    //void      clear();        // Destruct HAMT data structures only
    
    /**
      * Delete all items and structure.
      */
    void destroy(){
      if ( empty() ){ return; }

      ArrayMappedTrie.destroyAll( cast(ArrayMappedTrie *) root);

      // HashTrie is now empty
      root = null;
    }
    
    /**
      * Returns number of elements in tree.
      */
    @property count(){ return count;}
    
    /** 
      * Destructor clears all items.
      * A copy of each item is required for 
      * retention
      */      
    ~this(){ destroy(); }    
    
    void add(KeyType key, ValueType value) 
    {
      // forward to AMT add method
      amt.add(key,value);
      count += 1;
    }


private:
    // Each Node entry in the hash table is either terminal node
    // (a T pointer) or AMT data structure.
    //
    //        If a node pointer's LSB == 1 then AMT
    //            else T object pointer
    //
    // A one bit in the bit map represents a valid arc, while a zero an empty arc.
    // The pointers in the table are kept in sorted order and correspond to
    // the order of each one bit in the bit map.


    // Root Hash Table
    ArrayMappedTrie!(KeyType,ValueType,0) amt; 
    uint                                count = 0;
    Allocator                           allocator;
};



/**
  * Internal struct.
  */
package struct ArrayMappedTrie(KeyType, ValueType, AllocatorType = Mallocator) 
//if ( hasMember!(KeyType, "hashOf" ) ) // if isClass && has hashOf override && opequals override (just like AA's) 
{
  // TODO -- optimize:
  //  * Replace BitArray (unnecessarily big, needs external uint anyway)
  //  * Optimize for alignment
  // TODO -- evaluate appropriateness of ".hashOf" versus custom hash implementation
  // TODO -- add function attributes, e.g. pure, nothrow, trusted, etc.

  public:

    this( uint depthArg, AllocatorType allocArg )
    { depth = depthArg; allocator = allocArg; }

    /**
      Checks empty status by checking length of subTable. 
      An AMT is empty only if clear'ed or is the root node.  
      */
    bool empty() pure
    out(result)
    {
      if( result )
      { assert(internalBits == 0, "bitArray is not in sync with subTable"); }
    }
    body
    { return subTable.length == 0; }


    /**
      Returns value, if found. Else, null.
      Searches tree recursively
      */
    ValueType* find(KeyType key)
    {
      if (empty())
      { return null; }
      
      // Hash the key
      immutable auto bitIndex = this.getBitArrayIndex(key.hashOf());
      
      // Test bit index
      if (bitArray[bitIndex] == 0) 
      { return null; }
      
      auto varIndex = getTablePosition(bitIndex);
      assert(subTable.length() > varIndex);
      
      // Switch on the type of variant.
      // If ValueType, return the value found.
      // If AMT, recurse and search for the key deeper in the tree.
      auto var = subTable[varIndex];
      return var.visit!
      (
        (AMT* amt) =>
          { assert( amt !is null); return amt.find(key);},
        (ValueType* v) =>
          { assert( v !is null); return v; },
        () => 
          { assert("Logic error. Empty variant case should have been covered."); } )();
    }
    unittest
    {
      auto a = AMT!(int,string)(0);
      assert(a.empty());
      assert(a.find(2)==null); 
    }
    
    
    /**
      Membership test.
      */
    bool opBinaryRight(string op)(KeyType rhs)
      if (op == "in" )
    {
      return this.find(rhs) != null;
    }
    unittest
    {
      auto a = AMT!(int,double)(0);
      
    
    
    /** 
      * 
      */
    void insert( KeyType key, ValueType value, uint depth ){
      // If we're empty, insert to the first slot!
      if( items.length == 0 ){
        // TODO - Ask the allocator for a new array of size 1. 
        items ~= value;
        
        // Set the appropriate bit
        getBitIndex( key.hash() );
      } 
    }
    
    /**
      *
      */
    ValueType lookup(immutable uint hash) 
    {
    }
    
  package:
    alias AMT         = ArrayMappedTrie!(KeyType,ValueType,AllocatorType);
    alias ValueOrAMT  = Variant!(AMT*,ValueType*);
  
  private:  
    ValueOrAMT[]      subTable;
    uint              internalBits = 0;
    BitArray          bitArray = BitArray( internalBits.sizeof, cast(size_t*)&internalBits );
    
    uint              depth;
    AllocatorType     allocator;

    /**
      Translates the hash to a bit pattern representing the single "on" bit (the hash).
      E.g. hash = 8 => bit position = 100000000
      E.g. hash = 0 => bit position = 00000001
      depth is used to shift the correct bits into 'view' of the mask.
      */
    uint getBitArrayIndex(uint hash)
    {
      hash >>= depth * HashIndexBits;
      auto masked = hash & HashIndexMask;
      return 1 << masked; 
    }
  
  
    /**
      * Get the position of the item in the subarray, given the hash bit position into the map.
      * E.g. if the hash resolves to 18, but there are only 10 items in the array, the desired item index is 10.
      * If the hash resolves to 5, and there are 10 items in the array, the desired item index will be less than 10. 
      * This assumes the hash bit is set, and has been checked before calling.
      */
    auto getTablePosition( uint map, uint bitIndex )
    in
    {
      assert (bitArray[bitIndex] != 0 );
    }
    out (result)
    {
      assert( result < subTable.length );
    }
    body
    {
      return getBitCount(bitArray & (hashBitPosition - 1));
    }

}

