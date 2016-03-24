module hamtd;

import core.cpuid:hasPopcnt;
import core.bitop:popcnt;
import std.variant;
import std.traits;
import std.meta;
import std.experimental.allocator.mallocator:Mallocator;
import std.exception;
import std.bitmanip:BitArray;


/**
  References:
    - Ideal Hash Trees by Phil Bagwell - http://lampwww.epfl.ch/papers/idealhashtrees.pdf
    - Implementation in C++: https://github.com/chaelim/HAMT/
 */


/**
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

static this()
{  
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
  CTFE function to generate types specific to the HAMT and AMT types.
  Accepts either 16, 32 bit or 64 bit types. DRY.
  TODO -- Flesh out....
  */
/*
string create32Type( string aliasName, string structName )
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
{ alias HAMT32 = HashTrie!(uint,Args); }
template AMT32(Args...)
{ alias AMT32 = ArrayMappedTrie!(uint,Args); }

/**
  Primary HashTrie type.
  */
struct HashTrie(HashType, KeyType, ValueType, AllocatorType = Mallocator) 
  if (isPointer!ValueType) 
{
  public:

    this(this) @disable;

    this( AllocatorType a ){
      enforce(a !is null,"Allocator argument cannot be null");
      allocator = a;
    }
    
    ~this()
    { destroy(); }
    
    /**
      Removes tree structure. 
      If ValueType has reference semantics, the garbage collector will handle that memory.
      If it has value semantics, the 
      */ 
    void destroy()
    { root.destroy(); }
    
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
      * Returns number of elements in tree.
      */
    @property length(){ return count; }
    
    void add(KeyType key, ValueType value) 
    {
      // forward to AMT add method
      amt.add(key,value);
      count += 1;
    }


  private:
  // TODO -- Perhaps increase this for 64bit?
  immutable enum  NumSubHashBits = 5;
  immutable enum  SubHashMask = (1 << NumSubHashBits) - 1;
  
  // Once the maximum has been reached, rehash and dive deeper.
  immutable enum  SubHashesPerHash  = HashType.sizeof / SubHashMask;//((uint.sizeof * 8 + 7) / NumSubHashBits) * NumSubHashBits;
  immutable enum  RehashThreshold   = MaxHashBits / NumSubHashBits; // Can work past this...
  
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
  alias     AMTType = ArrayMappedTrie!(HashType,KeyType,ValueType,AllocatorType);
  AMTType   root    = AMTType(0,allocator); 
  uint      count   = 0;
  Allocator allocator;



  /**
    * Internal struct.
    */
  struct ArrayMappedTrie(HashType, KeyType, ValueType, AllocatorType = Mallocator) 
  //if ( hasMember!(KeyType, "hashOf" ) ) 
  // if isClass && has hashOf override && opequals override (just like AA's) 
  {
    // TODO -- optimize:
    //  * Replace BitArray (unnecessarily big, needs external uint anyway)
    //  * Optimize for alignment
    // TODO -- evaluate appropriateness of ".hashOf" versus custom hash implementation
    // TODO -- add function attributes, e.g. pure, nothrow, trusted, etc.
    public:
      this( uint depthArg, AllocatorType allocArg )
      { depth = depthArg; allocator = allocArg; }
      
      ~this()
      { destroy(); }

      /**
        For manual destruction.
        */
      void destroy()
      { allocator.dispose(subTable); }

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

      static if (isPointer!ValueType)
      {
      /**
        Returns value, if found. Else, null.
        Searches tree recursively.
        */
      import std.typecons:Nullable;
      Nullable!ValueType find(const ref KeyType key)
      {
        if (empty())
        { return Nullable!ValueType(); }
        
        // Hash the key
        immutable auto bitIndex = this.getBitArrayIndex(key.hashOf());
        
        // Test bit index
        if (bitArray[bitIndex] == 0) 
        { return Nullable!ValueType(); }
        
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
          (ValueType v) =>
            { assert( v !is null); return v; },
          () => 
            { assert("Logic error. Empty variant case should have been covered."); } )();
      }
      }//static if
      else // Value type must have value semantics
      {
        //rewrite find for value semantics.......Might need to keep two separate structs.
      }
      unittest
      {
        auto a = AMT32!(int,string)(0);
        assert(a.empty());
        assert(a.find(2)==null); 
      }
      
      
      /**
        Membership test.
        */
      bool opBinaryRight(string op)(const ref KeyType rhs)
        if (op == "in" )
      {
        return this.find(rhs) != null;
      }
      unittest
      {
        auto a = AMT32!(int,double)(0);
        assert( 1 !in a );
      }
      
      
      /** 
        * 
        */
      void insert( KeyType key, ValueType value )
      {
        // If we're empty, insert to the first slot!
        if( empty() )
        {
          subTable = allocator.makeArray!ValueOrAMT(1,value);
          
          // Set the appropriate bit
          getBitArrayIndex( key.hash() );
        } 
      }

    package:
      alias AMT         = ArrayMappedTrie!(KeyType,ValueType,AllocatorType);
      alias ValueOrAMT  = Variant!(AMT*,ValueType);
    
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
        Depth beyond sizeof(uint)/NumSubHashBits 
        */
      uint getBitArrayIndex(uint hash)
      {      
        hash >>= depth %  * NumSubHashBits;
        auto masked = hash & SubHashMask;
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
  }// struct ArrayMappedTrie
}//struct HashTrie
