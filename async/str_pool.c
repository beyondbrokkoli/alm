/* async/str_pool.c (alm-owned): the process-canonical string pool,
   the third stateful layer the substrate owns (trace plate, exec registry,
   strings).

   Layout contract (frozen):

     allocation: [8 bytes: i64 key] [N bytes: UTF-8] [1 byte: 0x00]
     handle:     pointer to the UTF-8 bytes — the canonical *const u8
     key:        STR_KEY_TAG | (fnv1a_64(bytes) & 0x3FFF_FFFF_FFFF_FFFF)
                 with STR_KEY_TAG = INT64_MIN (top two bits 10)

   The key is a pure function of the bytes, so the compiler can bake the
   same constant into IR for literal keys; the 8-byte prefix caches it so
   dynamic t[s] key extraction is one load (alm_str_key). The key derive
   here and in src/rt.rs (and the future backend constant folder) MUST stay
   byte-identical — it is a cross-module ABI contract, not an
   implementation detail.

   Allocator rule: THIS substrate is the sole allocator of interned
   strings, and interned strings are immortal (never freed). One
   allocator, zero frees — module boundaries cannot split an allocation.
   alm_str_register interns COPIES of .rodata literals and overwrites the
   caller's strtab slots with the canonical (prefixed) pointers, so no
   unprefixed static string ever masquerades as a pool handle.

   Traces: slot 8 (RT_STR_INTERN) on a miss-allocate, slot 9
   (RT_STR_POOL_HIT) on a dedup hit, poked anonymously — the pool cannot
   know the calling copy's exec id, so hits/misses ride the 0xFF event tag
   instead of an exec slot. */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "sys_sync.h"

/* alm_async.h declares the full contract; the unity build's include order
   owns vmath_thread_t, so this translation unit self-declares what it
   uses (the declarations must stay identical). */
void vx_trace_poke(uint8_t slot);
void vx_spin_wait(int* spin_count);

#define STR_KEY_TAG   ((int64_t)INT64_MIN)
#define STR_POOL_BUCKETS 4096

typedef struct StrNode {
    struct StrNode* next;
    char*           data; /* the [key][bytes][NUL] block */
    size_t          len;
} StrNode;

static StrNode* pool_buckets[STR_POOL_BUCKETS];

/* The pool is process-shared and mutable: vx_str_register runs in ctors
   (possibly several modules loading at once) and vx_str_intern is
   reachable from every coroutine worker pthread (the boundary builder
   dlsyms it), so bucket scan and head insert are a critical section —
   the substrate's house spinlock (TAS/CLR + vx_spin_wait, sys_sync.h).
   Nodes are immortal (one allocator, zero frees), so the lock has no
   ordering partner to deadlock against and readers never outlive it. */
static atomic_flag pool_lock = ATOMIC_FLAG_INIT;

static uint64_t fnv1a_64(const uint8_t* s, size_t len) {
    uint64_t h = 14695981039346656037ULL;
    for (size_t i = 0; i < len; i++) {
        h ^= s[i];
        h *= 1099511628211ULL;
    }
    return h;
}

static int64_t str_key_of(const uint8_t* s, size_t len) {
    return (int64_t)(STR_KEY_TAG | (int64_t)(fnv1a_64(s, len) &
                                             0x3FFFFFFFFFFFFFFFULL));
}

static const uint8_t* pool_intern(const uint8_t* s, size_t len) {
    int spin = 0;
    while (TAS(pool_lock)) {
        vx_spin_wait(&spin);
    }
    uint64_t h = fnv1a_64(s, len);
    StrNode** bucket = &pool_buckets[h % STR_POOL_BUCKETS];
    const uint8_t* out = NULL;
    for (StrNode* n = *bucket; n; n = n->next) {
        if (n->len == len && memcmp(n->data + 8, s, len) == 0) {
            out = (const uint8_t*)n->data + 8;
            break;
        }
    }
    if (out) {
        CLR(pool_lock);
        vx_trace_poke(9); /* RT_STR_POOL_HIT */
        return out;
    }
    char* block = malloc(8 + len + 1);
    if (!block) {
        CLR(pool_lock);
        return NULL;
    }
    int64_t key = str_key_of(s, len);
    memcpy(block, &key, 8);
    memcpy(block + 8, s, len);
    block[8 + len] = 0;
    StrNode* node = malloc(sizeof(StrNode));
    if (!node) {
        free(block);
        CLR(pool_lock);
        return NULL;
    }
    node->data = block;
    node->len = len;
    node->next = *bucket;
    *bucket = node;
    CLR(pool_lock);
    vx_trace_poke(8); /* RT_STR_INTERN */
    return (const uint8_t*)block + 8;
}

EXPORT const uint8_t* vx_str_intern(const uint8_t* s, size_t len) {
    if (!s) {
        return NULL;
    }
    return pool_intern(s, len);
}

/* Overwrites each strtab slot with the canonical (prefixed) pool pointer.
   The strtab is emitted as a writable LLVM `global`; ctors run before any
   module code, so by the time a literal handle is used it is prefixed. */
EXPORT void vx_str_register(const uint8_t** strtab, int64_t n) {
    for (int64_t i = 0; i < n; i++) {
        const uint8_t* lit = strtab[i];
        if (lit) {
            strtab[i] = pool_intern(lit, strlen((const char*)lit));
        }
    }
}
