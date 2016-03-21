module hamtd;

import core.cpuid:hasPopcnt;
import core.bitop:popcnt;
import core.bitop:_popcnt;
/**
 *  References:
 *      - Ideal Hash Trees by Phil Bagwell (This is main paper the orignal ideas came from)
 *      - Ideal Hash Tries: an implementation in C++
 *          http://www.altdevblogaday.com/2011/03/22/ideal-hash-tries-an-implementation-in-c/
 */

uint rotl32 (uint x, byte r) {
    return (x << r) | (x >> (32 - r));
}

ulong rotl64 (ulong x, byte r) {
    return (x << r) | (x >> (64 - r));
}

ulong rotr (uint x, byte r) {
    return (x >> r) | (x << (32 - r))
}

ulong rotr (ulong x, byte r) {
    return (x >> r) | (x << (64 - r))
}

/** 
*   Some bit twiddling helpers
*
*   GetBitCount function
*        from http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
*
**/

// IF __POPCNT AVAILABLE
static this(){
  if( !core.cpuid.hasPopcnt() ){
    uint GetBitCount(uint v) {
      v = v - ((v >> 1) & 0x55555555);                    // reuse input as temporary
      v = (v & 0x33333333) + ((v >> 2) & 0x33333333);     // temp
      return ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24; // count
    }
  }
}

/**
if( 64bit target ){

inline uint GetBitCount (ulong v) {
    return __popcnt64(v);
}

**/

// MurmurHash3
//uint MurmurHash3_x86_32(const void * key, int len, uint_t seed);


//===========================================================================
//    THashKey32
//    (Helper template class to get 32bit integer hash key value for POD types)
//===========================================================================
template <class T>
class THashKey32 {
    static const uint MURMUR_HASH3_SEED = sizeof(T);

public:
    THashKey32() : m_key(0) { }
    THashKey32(const T & key) : m_key(key) { }
    inline bool operator== (const THashKey32 & rhs) const { return m_key == rhs.m_key; }
    inline operator T () const { return m_key; }
    inline uint GetHash() const;
    inline const T & Get() const { return m_key; }
    inline void Set(const T & key) { m_key = key; }

protected:
    T        m_key;
};

/**
 * Generic Hash function for POD types
 */
template <class T>
inline uint THashKey32<T>::GetHash() const {
    return MurmurHash3_x86_32(
        (const void *)&m_value,
        sizeof(m_value),
        MURMUR_HASH3_SEED
    );
}

// Integer hash functions based on
//    http://www.cris.com/~Ttwang/tech/inthash.htm

/**
 * Specialization for 32 bit interger key
 */
template <>
inline uint THashKey32<int>::GetHash() const {
    uint key = (uint)m_key;
    key = ~key + (key << 15); // key = (key << 15) - key - 1;
    key ^= ROTR64(key, 12);
    key += (key << 2);
    key ^= ROTR64(key, 4);
    key *= 2057; // key = (key + (key << 3)) + (key << 11);
    key ^= ROTR64(key, 16);
    return key;
}

/**
 * Specialization for 32 bit interger key
 */
template <>
inline uint THashKey32<uint>::GetHash() const {
    uint key = m_key;
    key = ~key + (key << 15); // key = (key << 15) - key - 1;
    key ^= ROTR64(key, 12);
    key += (key << 2);
    key ^= ROTR64(key, 4);
    key *= 2057; // key = (key + (key << 3)) + (key << 11);
    key ^= ROTR64(key, 16);
    return key;
}

/**
 * Specialization for 64 bit interger key (64 bit to 32 bit hash)
 */
template <>
inline uint THashKey32<long>::GetHash() const {
    ulong key = (ulong)m_key;
    key = (~key) + (key << 18); // key = (key << 18) - key - 1;
    key ^= ROTR64(key, 31);
    key *= 21; // key = (key + (key << 2)) + (key << 4);
    key ^= ROTR64(key, 11);
    key += (key << 6);
    key ^= ROTR64(key, 22);
    return (uint)key;
}

/**
 * Specialization for 64 bit interger key (64 bit to 32 bit hash)
 */
template <>
inline uint THashKey32<ulong>::GetHash() const {
    ulong key = m_key;
    key = (~key) + (key << 18); // key = (key << 18) - key - 1;
    key ^= ROTR64(key, 31);
    key *= 21; // key = (key + (key << 2)) + (key << 4);
    key ^= ROTR64(key, 11);
    key += (key << 6);
    key ^= ROTR64(key, 22);
    return (uint)key;
}

//===========================================================================
//    String Helper functions
//===========================================================================

inline size_t StrLen(const char str[]) {
    return strlen(str);
}

inline size_t StrLen(const wchar_t str[]) {
    return wcslen(str);
}

inline int StrCmp(const char str1[], const char str2[]) {
    return strcmp(str1, str2);
}

inline int StrCmp(const wchar_t str1[], const wchar_t str2[]) {
    return wcscmp(str1, str2);
}

inline int StrCmpI(const char str1[], const char str2[]) {
    return _stricmp(str1, str2);
}

inline int StrCmpI(const wchar_t str1[], const wchar_t str2[]) {
    return _wcsicmp (str1, str2);
}

inline char * StrDup(const char str[]) {
    return _strdup(str);
}

inline wchar_t * StrDup(const wchar_t str[]) {
    return _wcsdup(str);
}


//===========================================================================
//    TStrCmp and TStrCmpI
//===========================================================================
template<class CharType>
class TStrCmp {
public:
    static int StrCmp(const CharType str1[], const CharType str2[]) {
        return ::StrCmp(str1, str2);
    }
};

template<class CharType>
class TStrCmpI {
public:
    static int StrCmp(const CharType str1[], const CharType str2[]) {
        return ::StrCmpI(str1, str2);
    }
};


//===========================================================================
//    THashKeyStr
//===========================================================================
template<class CharType, class Cmp>
class THashKeyStrPtr;

template<class CharType, class Cmp = TStrCmp<CharType> >
class THashKeyStr {
public:
    bool operator== (const THashKeyStr & rhs) const {
        return (Cmp::StrCmp(m_str, rhs.m_str) == 0);
    }

    uint GetHash () const {
        if (m_str != NULL) {
            size_t strLen = StrLen(m_str);
            return MurmurHash3_x86_32(
                (const void *)m_str,
                sizeof(CharType) * strLen,
                strLen    // use string length as seed value
            );
        }
        else
            return 0;
    }
    const CharType * GetString () const { return m_str; }

protected:
    THashKeyStr() : m_str(NULL) { }
    virtual ~THashKeyStr() { }

    const CharType * m_str;

    friend class THashKeyStrPtr<CharType, Cmp>;
};

template<class CharType, class Cmp = TStrCmp<CharType> >
class THashKeyStrCopy : public THashKeyStr<CharType, Cmp> {
public:
    THashKeyStrCopy() { }
    THashKeyStrCopy(const CharType str[]) { SetString(str); }
    ~THashKeyStrCopy() {
        free(const_cast<CharType *>(THashKeyStr<CharType>::m_str));
    }

    void SetString(const CharType str[]) {
        free(const_cast<CharType *>(THashKeyStr<CharType>::m_str));
        THashKeyStr<CharType>::m_str = str ? StrDup(str) : NULL;
    }
};

template<class CharType, class Cmp = TStrCmp<CharType> >
class THashKeyStrPtr : public THashKeyStr<CharType, Cmp> {
public:
    THashKeyStrPtr() { }
    THashKeyStrPtr(const CharType str[]) { SetString(str); }
    THashKeyStrPtr(const THashKeyStr<CharType, Cmp> & rhs) {
        THashKeyStr<CharType, Cmp>::m_str = rhs.m_str;
    }
    THashKeyStrPtr & operator=(const THashKeyStr<CharType, Cmp> & rhs) {
        THashKeyStr<CharType, Cmp>::m_str = rhs.m_str;
        return *this;
    }
    THashKeyStrPtr & operator=(const THashKeyStrPtr<CharType, Cmp> & rhs) {
        THashKeyStr<CharType, Cmp>::m_str = rhs.m_str;
        return *this;
    }

    void SetString (const CharType str[]) {
        THashKeyStr<CharType, Cmp>::m_str = str;
    }
};

// Typedefs for convenience
typedef THashKeyStrCopy<wchar_t>                        CHashKeyStr;
typedef THashKeyStrPtr <wchar_t>                        CHashKeyStrPtr;
typedef THashKeyStrCopy<char>                           CHashKeyStrAnsiChar;
typedef THashKeyStrPtr <char>                           CHashKeyStrPtrAnsiChar;

typedef THashKeyStrCopy<wchar_t, TStrCmpI<wchar_t> >    CHashKeyStrI;
typedef THashKeyStrPtr <wchar_t, TStrCmpI<wchar_t> >    CHashKeyStrPtrI;
typedef THashKeyStrCopy<char, TStrCmpI<char> >          CHashKeyStrAnsiCharI;
typedef THashKeyStrPtr <char, TStrCmpI<char> >          CHashKeyStrPtrAnsiCharI;


/****************************************************************************
*
*   THashTrie
*
*   Template class for HAMT (Hash Array Mapped Trie)
*
**/

template <class T, class K>
class THashTrie {
private:
    // Use the least significant bit as reference marker
    static const uint_ptr   AMT_MARK_BIT    = 1;    // Using LSB for marking AMT (sub-trie) data structure
    static const uint     HASH_INDEX_BITS = 5;
    static const uint     HASH_INDEX_MASK = (1 << HASH_INDEX_BITS) - 1;
    // Ceiling to 8 bits boundary to use all 32 bits.
    static const uint     MAX_HASH_BITS   = ((sizeof(uint) * 8 + 7) / HASH_INDEX_BITS) * HASH_INDEX_BITS;
    static const uint     MAX_HAMT_DEPTH  = MAX_HASH_BITS / HASH_INDEX_BITS;

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

    struct ArrayMappedTrie {
        uint  m_bitmap;
        T *     m_subHash[1];
        // Do not add more data below
        // New data should be added before m_subHash

        inline T ** Lookup(uint hashIndex);
        inline T ** LookupLinear(const K & key);

        static T ** Alloc1(
            uint    bitIndex,
            T **    slotToReplace
        );
        static T ** Alloc2(
            uint  hashIndex,
            T *     node,
            uint  oldHashIndex,
            T *     oldNode,
            T **    slotToReplace
        );
        static T ** Alloc2Linear(
            T *     node,
            T *     oldNode,
            T **    slotToReplace
        );

        static ArrayMappedTrie * Insert(
            ArrayMappedTrie * amt,
            uint      hashIndex,
            T *         node,
            T **        slotToReplace
        );
        static ArrayMappedTrie * AppendLinear(
            ArrayMappedTrie *   amt,
            T *         node,
            T **        slotToReplace
        );
        static ArrayMappedTrie * Resize(
            ArrayMappedTrie * amt,
            int         oldSize,
            int         deltasize,
            int         idx
        );

        static void ClearAll(ArrayMappedTrie * amt, uint depth=0);
        static void DestroyAll(ArrayMappedTrie * amt, uint depth=0);
    };

    // Root Hash Table
    T *         m_root;
    uint      m_count;

public:
    THashTrie() : m_root(NULL), m_count(0) { }
    ~THashTrie() { Clear(); }

public:
    void Add(T * node);
    T * Find(const K & key);
    T * Remove(const K & key);
    bool Empty();
    uint GetCount() { return m_count; }
    void Clear();        // Destruct HAMT data structures only
    void Destroy();    // Destruct HAMT data structures as well as containing objects
};


//===========================================================================
//    THashTrie<T, K>::ArrayMappedTrie Implementation
//===========================================================================

// helpers to search for a given entry
// this function counts bits in order to return the correct slot for a given hash
template<class T, class K>
T ** THashTrie<T, K>::ArrayMappedTrie::Lookup(uint hashIndex) {
    assert(hashIndex < (1 << HASH_INDEX_BITS));
    uint bitPos = (uint)1 << hashIndex;
    if ((m_bitmap & bitPos) == 0)
        return NULL;
    else
        return &m_subHash[GetBitCount(m_bitmap & (bitPos - 1))];
}

template<class T, class K>
T ** THashTrie<T, K>::ArrayMappedTrie::LookupLinear(const K & key) {
    // Linear search
    T ** cur = m_subHash;
    T ** end = m_subHash + m_bitmap;
    for (; cur < end; cur++) {
        if (**cur == key)
            return cur;
    }
    // Not found
    return NULL;
}

template<class T, class K>
T ** THashTrie<T, K>::ArrayMappedTrie::Alloc1(uint bitIndex, T ** slotToReplace) {
    // Assert (0 <= bitIndex && bitIndex < 31);
    ArrayMappedTrie * amt = (ArrayMappedTrie *)malloc(sizeof(ArrayMappedTrie));
    amt->m_bitmap = 1 << bitIndex;
    *slotToReplace = (T *)((uint_ptr)amt | AMT_MARK_BIT);
    return amt->m_subHash;
}

template<class T, class K>
T ** THashTrie<T, K>::ArrayMappedTrie::Alloc2(
    uint      hashIndex,
    T *         node,
    uint      oldHashIndex,
    T *         oldNode,
    T **        slotToReplace
) {
    // Allocates a node with room for 2 elements
    ArrayMappedTrie * amt = (ArrayMappedTrie *)malloc(
          sizeof(ArrayMappedTrie)
        + sizeof(T *)
    );
    amt->m_bitmap = \
        ((uint)1 << hashIndex) | ((uint)1 << oldHashIndex);

    // Sort them in order and return new node
    if (hashIndex < oldHashIndex) {
        amt->m_subHash[0] = node;
        amt->m_subHash[1] = oldNode;
    }
    else {
        amt->m_subHash[0] = oldNode;
        amt->m_subHash[1] = node;
    }

    *slotToReplace = (T *)((uint_ptr)amt | AMT_MARK_BIT);;
    return amt->m_subHash;
}

template<class T, class K>
T ** THashTrie<T, K>::ArrayMappedTrie::Alloc2Linear(
    T *        node,
    T *        oldNode,
    T **    slotToReplace
) {
    // Allocates a node with room for 2 elements
    ArrayMappedTrie * amt = (ArrayMappedTrie *)malloc(
          sizeof(ArrayMappedTrie)
        + sizeof(T *)
    );
    amt->m_bitmap = 2;    // Number of entry in the linear search array
    amt->m_subHash[0] = node;
    amt->m_subHash[1] = oldNode;
    *slotToReplace = (T *)((uint_ptr)amt | AMT_MARK_BIT);
    return amt->m_subHash;
}

template<class T, class K>
typename THashTrie<T, K>::ArrayMappedTrie *
THashTrie<T, K>::ArrayMappedTrie::Insert(
    ArrayMappedTrie * amt,
    uint      hashIndex,
    T *         node,
    T **        slotToReplace
) {
    uint bitPos = (uint)1 << hashIndex;
    assert((amt->m_bitmap & bitPos) == 0);

    uint numBitsBelow = GetBitCount(amt->m_bitmap & (bitPos-1));
    amt = Resize(amt, GetBitCount(amt->m_bitmap), 1, numBitsBelow);
    amt->m_bitmap |= bitPos;
    amt->m_subHash[numBitsBelow] = node;
    *slotToReplace = (T *)((uint_ptr)amt | AMT_MARK_BIT);
    return amt;
}

template<class T, class K>
typename THashTrie<T, K>::ArrayMappedTrie *
THashTrie<T, K>::ArrayMappedTrie::AppendLinear(
    ArrayMappedTrie * amt,
    T *         node,
    T **        slotToReplace
) {
    amt = Resize(amt, amt->m_bitmap, 1, amt->m_bitmap);
    amt->m_subHash[amt->m_bitmap] = node;
    amt->m_bitmap++;
    *slotToReplace = (T *)((uint_ptr)amt | AMT_MARK_BIT);
    return amt;
}

// memory allocation all in this function. (re)allocates n,
// copies old m_data, and inserts space at index 'idx'
template<class T, class K>
typename THashTrie<T, K>::ArrayMappedTrie *
THashTrie<T,K>::ArrayMappedTrie::Resize(
    ArrayMappedTrie * amt,
    int        oldSize,
    int        deltaSize,
    int        idx
) {
    assert(deltaSize != 0);
    int newSize = oldSize + deltaSize;
    assert(newSize > 0);

    // if it shrinks then (idx + deltasize, idx) will be removed
    if (deltaSize < 0) {
        memmove(
            amt->m_subHash + idx,
            amt->m_subHash + idx - deltaSize,
            (newSize - idx) * sizeof(T *)
        );
    }

    amt = (ArrayMappedTrie *)realloc(
        amt,
        sizeof(ArrayMappedTrie)
            + (newSize - 1) * sizeof(T *)
    );

    // If it grows then (idx, idx + deltasize) will be inserted
    if (deltaSize > 0) {
        memmove(
            amt->m_subHash + idx + deltaSize,
            amt->m_subHash + idx,
            (oldSize - idx) * sizeof(T *)
        ); // shuffle tail to make room
    }

    return amt;
}


/*
 * Destroy HashTrie including pertaining sub-tries
 * NOTE: It does NOT destroy the objects in leaf nodes.
 */
template<class T, class K>
void THashTrie<T, K>::ArrayMappedTrie::ClearAll(
    ArrayMappedTrie * amt,
    uint depth
) {
    // If this is a leaf node, do nothing
    if (((uint_ptr)amt & AMT_MARK_BIT) == 0)
        return;

    amt = (ArrayMappedTrie *)((uint_ptr)amt & (~AMT_MARK_BIT));
    if (depth < MAX_HAMT_DEPTH) {
        T ** cur = amt->m_subHash;
        T ** end = amt->m_subHash + GetBitCount(amt->m_bitmap);
        for (; cur < end; cur++)
            ClearAll((ArrayMappedTrie *)*cur, depth + 1);
    }
    free(amt);
}

/*
 * Destroy HashTrie including pertaining sub-tries and containing objects
 * NOTE: It DOES destory (delete) the objects in leaf nodes.
 */
template<class T, class K>
void THashTrie<T, K>::ArrayMappedTrie::DestroyAll(
    ArrayMappedTrie * amt,
    uint depth
) {
    // If this is a leaf node just destroy the conatining object T
    if (((uint_ptr)amt & AMT_MARK_BIT) == 0) {
        delete ((T *)amt);
        return;
    }

    amt = (ArrayMappedTrie *)((uint_ptr)amt & (~AMT_MARK_BIT));
    if (depth < MAX_HAMT_DEPTH) {
        T ** cur = amt->m_subHash;
        T ** end = amt->m_subHash + GetBitCount(amt->m_bitmap);
        for (; cur < end; cur++)
            DestroyAll((ArrayMappedTrie *)*cur, depth + 1);
    }
    else {
        T ** cur = amt->m_subHash;
        T ** end = amt->m_subHash + amt->m_bitmap;
        for (; cur < end; cur++)
            delete ((T * )*cur);
    }

    free(amt);
}


#if _MSC_VER
inline bool HasAMTMarkBit (uint_ptr ptr) {
    return _bittest((const long *)&ptr, 0) != 0;
}
#else
inline bool HasAMTMarkBit (uint_ptr ptr) {
    return (ptr & 1) != 0;
}
#endif

//===========================================================================
//    THashTrie<T, K> Implementation
//===========================================================================

template<class T, class K>
inline void THashTrie<T, K>::Add(T * node) {
    // If hash trie is empty just add value/pair node and set it as root
    if (Empty()) {
        m_root = node;
        m_count++;
        return;
    }

    // Get hash value
    uint hash = node->GetHash();
    uint bitShifts = 0;
    T ** slot = &m_root;    // First slot is the root node
    for (;;) {
        // Leaf node (a T node pointer)?
        if (!HasAMTMarkBit((uint_ptr)*slot)) {
            // Replace if a node already exists with same key.
            // Caller is responsible for checking if a different object
            // with same key already exists and prevent memory leak.
            if (**slot == *node) {
                *slot = node;
                return;
            }

            // Hash collision detected:
            //      Replace this leaf with an AMT node to resolve the collision.
            //    The existing key must be replaced with a sub-hash table and
            //    the next 5 bit hash of the existing key computed. If there is still
            //    a collision then this process is repeated until no collision occurs.
            //    The existing key is then inserted in the new sub-hash table and
            //    the new key added.

            T *        oldNode = *slot;
            uint    oldHash = oldNode->GetHash() >> bitShifts;

            // As long as the hashes match, we have to create single element
            // AMT internal nodes. this loop is hopefully nearly always run 0 time.
            while (bitShifts < MAX_HASH_BITS && (oldHash & HASH_INDEX_MASK) == (hash & HASH_INDEX_MASK)) {
                slot = ArrayMappedTrie::Alloc1(hash & HASH_INDEX_MASK, slot);
                bitShifts += HASH_INDEX_BITS;
                hash     >>= HASH_INDEX_BITS;
                oldHash  >>= HASH_INDEX_BITS;
            }

            if (bitShifts < MAX_HASH_BITS) {
                ArrayMappedTrie::Alloc2(
                    hash & HASH_INDEX_MASK,
                    node,
                    oldHash & HASH_INDEX_MASK,
                    oldNode,
                    slot
                );
            }
            else {
                // Consumed all hash bits, alloc and init a linear search table
                ArrayMappedTrie::Alloc2Linear(
                    node,
                    oldNode,
                    slot
                );
            }

            m_count++;
            break;
        }

        //
        // It's an Array Mapped Trie (sub-trie)
        //
        ArrayMappedTrie * amt = (ArrayMappedTrie *)((uint_ptr)*slot & (~AMT_MARK_BIT));
        T ** childSlot;
        if (bitShifts >= MAX_HASH_BITS) {
            // Consumed all hash bits. Add to the linear search array.
            childSlot = amt->LookupLinear(*node);
            if (childSlot == NULL) {
                ArrayMappedTrie::AppendLinear(amt, node, slot);
                m_count++;
            }
            else
                *slot = node;     // If the same key node already exists then replace
            break;
        }

        childSlot = amt->Lookup(hash & HASH_INDEX_MASK);
        if (childSlot == NULL) {
            amt = ArrayMappedTrie::Insert(
                amt,
                hash & HASH_INDEX_MASK,
                node,
                slot
            );
            m_count++;
            break;
        }

        // Go to next sub-trie level
        slot = childSlot;
        bitShifts += HASH_INDEX_BITS;
        hash     >>= HASH_INDEX_BITS;
    }    // for (;;)
}

template<class T, class K>
T * THashTrie<T, K>::Find(const K & key) {
    // Hash trie is empty?
    if (Empty())
        return NULL;

    // Get hash value
    uint hash = key.GetHash();
    uint bitShifts = 0;
    const T * slot = m_root;    // First slot is the root node
    for (;;) {
        // Leaf node (a T node pointer)?
        if (((uint_ptr)slot & AMT_MARK_BIT) == 0)
            return (*slot == key) ? (T *)slot : NULL;

        //
        // It's an Array Mapped Trie (sub-trie)
        //
        ArrayMappedTrie * amt = (ArrayMappedTrie *)((uint_ptr)slot & (~AMT_MARK_BIT));
        if (bitShifts >= MAX_HASH_BITS) {
            // Consumed all hash bits. Run linear search.
            T ** linearSlot = amt->LookupLinear(key);
            return (linearSlot != NULL) ? *(linearSlot) : NULL;
        }

        T ** childSlot = amt->Lookup(hash & HASH_INDEX_MASK);
        if (childSlot == NULL)
            return NULL;

        // Go to next sub-trie level
        slot = *childSlot;
        bitShifts += HASH_INDEX_BITS;
        hash     >>= HASH_INDEX_BITS;
    }

    // !!! SHOULD NEVER BE HERE !!!
    assert(false);
}

template<class T, class K>
T * THashTrie<T, K>::Remove(const K & key) {
    T ** slots[MAX_HAMT_DEPTH + 2];
    slots[0] = &m_root;

    ArrayMappedTrie * amts[MAX_HAMT_DEPTH + 2];
    amts[0] = NULL;

    uint hash = key.GetHash();
    //
    // First find the leaf node that we want to delete
    //
    int depth = 0;
    for (; depth <= MAX_HAMT_DEPTH; ++depth, hash >>= HASH_INDEX_BITS) {
        // Leaf node?
        if (((uint_ptr)*slots[depth] & AMT_MARK_BIT) == 0) {
            amts[depth] = NULL;
            if (!(**slots[depth] == key))
                return NULL;
            break;
        }
        else {
            // It's an AMT node
            ArrayMappedTrie * amt = amts[depth] = \
                (ArrayMappedTrie *)((uint_ptr)*slots[depth] & (~AMT_MARK_BIT));
            slots[depth + 1] = (depth >= MAX_HAMT_DEPTH) ? \
                    amt->LookupLinear(key) : amt->Lookup(hash & HASH_INDEX_MASK);
            if (slots[depth + 1] == NULL)
                return NULL;
        }
    }

    // Get the node will be returned
    T * ret = *slots[depth];

    // we are going to have to delete an entry from the internal node at amts[depth]
    while (--depth >= 0) {
        int oldsize = depth >= MAX_HAMT_DEPTH ? \
                (int)(amts[depth]->m_bitmap) :
                (int)(GetBitCount(amts[depth]->m_bitmap));
        int oldidx  = (int)(slots[depth + 1] - amts[depth]->m_subHash);

        // the second condition is that the remaining entry is a leaf
        if (oldsize == 2 && ((uint_ptr)(amts[depth]->m_subHash[!oldidx]) & AMT_MARK_BIT) == 0) {
            // we no longer need this node; just fold the remaining entry,
            // which must be a leaf, into the parent and free this node
            *(slots[depth]) = amts[depth]->m_subHash[!oldidx];
            free(amts[depth]);
            break;
        }

        // resize this node down by a bit, and update the m_usedBitMap bitfield
        if (oldsize > 1) {
            ArrayMappedTrie * amt = ArrayMappedTrie::Resize(amts[depth], oldsize, -1, oldidx);
            amt->m_bitmap = (depth >= MAX_HAMT_DEPTH) ? \
                (amt->m_bitmap - 1) : ClearNthSetBit(amt->m_bitmap, oldidx);
            *(slots[depth]) = (T *)((uint_ptr)amt | AMT_MARK_BIT);    // update the parent slot to point to the resized node
            break;
        }
        free(amts[depth]);    // oldsize==1. delete this node, and then loop to kill the parent too!
    }

    // No node exists in the HashTrie any more
    if (depth < 0)
        m_root = NULL;

    m_count--;
    return ret;
}

template<class T, class K>
inline bool THashTrie<T, K>::Empty() {
    return m_root == NULL;
}

template<class T, class K>
inline void THashTrie<T, K>::Clear() {
    if (Empty())
        return;

    ArrayMappedTrie::ClearAll((ArrayMappedTrie *)m_root);

    // HashTrie is now empty
    m_root = NULL;
}


template<class T, class K>
inline void THashTrie<T, K>::Destroy() {
    if (Empty())
        return;

    ArrayMappedTrie::DestroyAll((ArrayMappedTrie *)m_root);

    // HashTrie is now empty
    m_root = NULL;
}

#endif // if __HASH_TRIE_H__