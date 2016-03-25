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
{ alias HAMT32 = HashTrie!(uint,Args); }


/**
  HAMT type.
  * Size of the hash type determines:
    * Length of the ValueType list and lookup table.
    * Depth threshold at which the hash must be rehashed (at 5 bit chunks, 32 bits gives 6 chunks/levels; 64bits/6bit chunks -> 10 chunks/levels;etc).
    * Can be 32 bits now. Possible 16,32,64 bits support in future. 
  KeyType must be hashable.
  ValueType must be default constructible or a pointer type.
  
  TODO -- Create a custom allocator: retains pools of arrays of various sizes. Minimum retention size for each pool. 
  
  TODO -- Specialize for pointer and non-pointer ValueType's a la "static if (isPointer!ValueType)"
    - Value semantics for ValueType's will remove a layer of indirection from retrieving values, but increase the size of the resulting tables.
    - Reference semantics is the opposite: smaller table sizes, but an extra layer of indirection. 
    - Test the speed of each * different bit widths for the hash type.
  */
struct HAMT(HashType, KeyType, ValueType, AllocatorType = Mallocator) 
// TODO -- if ( hasMember!(KeyType, "hashOf" ) ) 
// TODO -- if isClass && has hashOf override && opequals override (just like AA's) 
{
private:
  alias 
  alias ThisType     = HAMT!(KeyType,ValueType,AllocatorType);
  alias ValueOrHAMT  = Variant!(ThisType*,ValueType*);
  // TODO -- Create POD quantity type for bits?
  // TODO -- Perhaps increase this for 64bit?
  immutable enum  SubHashSize = 5; // In bits
  immutable enum  SubHashMask = (1 << SubHashSize) - 1;
  
  // SubHashesPerHash is used to determine when to rehash the key, i.e. when the limit of unique chunks of the hash has been met. 
  immutable enum  SubHashesPerHash      = HashType.sizeof / SubHashSize;//((uint.sizeof * 8 + 7) / SubHashSize) * SubHashSize;
  immutable enum  RehashThresholdDepth  = SubHashesPerHash / SubHashSize;
  
  // Each Node entry in the hash table is either terminal node
  // (a ValueType pointer) or HAMT data structure.
  // A one bit in the bit map represents a valid arc, while a zero an empty arc.
  // The pointers in the table are kept in sorted order and correspond to
  // the order of each one bit in the bit map.
  // TODO -- optimize:
  //  * Replace BitArray (unnecessarily big, needs external uint anyway)
  //  * Optimize for alignment
  // TODO -- evaluate appropriateness of ".hashOf" versus custom hash implementation
  // TODO -- add function attributes, e.g. pure, nothrow, trusted, etc.
  public:
    /**
      */
    this( AllocatorType a )
    {
      enforce(a !is null, "Allocator argument cannot be null");
      this(0, a);
    } 
    
  private
  {
    /**
      Private constructor allows initialization of depth argument to be something other than 0 (root).
      */
    this( uint depthArg, AllocatorType allocArg )
    { 
      allocator = allocArg;
      depth = depthArg;
    }
    
    bool isRoot() pure nothrow @safe
    { return depth == 0; }
  }
  
  
  /**
    Manual and automatic destruction.
    */
  void destroy()
  { allocator.dispose(subArray); }
  ~this()
  { destroy(); }

  
  /**
    Returns number of elements in entire tree. 
    */
  auto length()
  { return count; }


  /**
    Checks empty status by checking count. 
    */
  bool empty() pure
  out(result)
  {
    if( result )
    { 
      assert(internalBits == 0, "bitArray is not in sync with subArray");
      assert(subArray.length == 0); 
    }
  }
  body
  {
    return count() == 0; 
  }
  
  
  /**
    Returns value, if found. Else, null.
    Searches tree recursively.
    */
  ValueType* find(const ref KeyType key)
  {
    if (empty())
    { return null; }
    
    // Hash the key
    immutable auto bitIndex = this.getBitArrayIndex(key.hashOf());
    
    // Test bit index
    if (bitArray[bitIndex] == 0) 
    { return null; }
    
    auto varIndex = getTablePosition(bitIndex);
    assert(subArray.length() > varIndex);
    
    // Switch on the type of variant.
    // If ValueType, return the value found.
    // If HAMT, recurse and search for the key deeper in the tree.
    auto var = subArray[varIndex];
    return var.visit!
    (
      (ThisType* hamt) =>
        { assert( hamt !is null); return hamt.find(key);},
      (ValueType* v) =>
        { assert( v !is null); return v; },
      () => 
        { assert("Logic error. Empty variant case should have been covered."); } )();
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
    Uses allocator to create a new table of the given desired size. 
    Old table values are copied to the new table.
    The old table is disposed via the allocator.
      
    TODO -- Does marking the return type as "ref" help?
    */
  ValueOrHAMT[] reallocateSubArray(ref ValueOrHAMT[] oldTable, size_t desiredSize )
  {
    ValueOrHAMT[] newTable = allocator.makeArray!ValueOrHAMT(desiredSize, null);
    newTable[] = oldTable;
    allocator.dispose(oldTable);
    return newTable;
  }
  
  
  /** 
    * 
    */
  void insert( KeyType key, ValueType value )
  {
    auto bitIndex = getBitArrayIndex(key.hashOf());
    
    // If desired slot is not occupied, fill it.
    if (empty() || bitArray[bitIndex] == false)
    {
      auto varIndex = getTablePosition(bitIndex);
      // If the subArray size is too small, realocate.
      if ( subArray.length <= varIndex )
      {
        subArray = reallocateSubArray(subArray,subArray.length+1); 
        // TODO -- More complex or abstract logic needed for reallocation?
        //    * Could shrink array. Now only grows.
        //    * Optimal desired size when growing? Shrinking?
      }
      
      // Set the appropriate bit
      bitArray[bitIndex] = true;
      count += 1;
      return;
    }
    
    
  }


private:  
  /**
    Translates the hash to a bit pattern representing the single "on" bit (the hash).
    E.g. hash = 8 => bit position = 100000000
    E.g. hash = 0 => bit position = 00000001
    depth is used to shift the correct bits into 'view' of the mask.
    Depth beyond sizeof(uint)/SubHashSize 
    */
  uint getBitArrayIndex(uint hash)
  {      
    hash >>= depth %  * SubHashSize;
    auto masked = hash & SubHashMask;
    return 1 << masked; 
  }


  /**
    Get the position of the item in the subarray, given the hash bit position into the map.
    The subArray is kept "sorted", in that it's sparsely populated, the filled slots are contiguous, and the filled slots are at the front of the subArray.
    If the hash resolves to 18, but there are only 10 items in the array, the desired item index is 10.
    If the hash resolves to 5, and there are 10 items in the array, the desired item index will be less than 10. 
    */
  auto getTablePosition( uint map, uint bitIndex )
  {
    return getBitCount(bitArray & (hashBitPosition - 1));
  }
  
  
private:
  ValueOrHAMT[]     subArray;
  uint              internalBits = 0;
  BitArray          bitArray = BitArray( internalBits.sizeof, cast(size_t*)&internalBits );
  
  uint              depth;
  size_t            count;
  AllocatorType     allocator;
}


// struct HashTrie(HashType, KeyType, ValueType, AllocatorType = Mallocator) 
//   if (isPointer!ValueType) 
// {
//   public:

//     this(this) @disable;
//     this( AllocatorType a ){
//       enforce(a !is null, "Allocator argument cannot be null");
//       allocator = a;
//     }
    
//     /**
//       Removes tree structure. 
//       If ValueType has reference semantics, the garbage collector will handle that memory.
//       If it has value semantics, the 
//       */ 
//     void destroy()
//     { root.destroy(); }
//     ~this()
//     { destroy(); }
    
//     /** TODO -- add index operators;
//         TODO -- funcs to implement:
//           * insert, remove, "in", indexOp, indexAssignOp, 
//     */ 
//     /** 
//       *
//       */
//     bool empty() { return amt.empty(); }

//     /**
//       * Returns number of elements in tree.
//       */
//     @property length(){ return count; }
    
//     void insert(KeyType key, ValueType value) 
//     {
//       // forward to AMT add method
//       root.insert(key,value);
//       count += 1;
//     }


//   private:


//   // Root Hash Table
//   alias     AMTType = ArrayMappedTrie!(HashType,KeyType,ValueType,AllocatorType);
//   AMTType   root    = AMTType(0,allocator); 
//   uint      count   = 0;
//   Allocator allocator;
// }//struct HashTrie