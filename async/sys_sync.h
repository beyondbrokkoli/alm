/* async/sys_sync.h — the macro block of demo_engine/host/ipc/sys_sync.c,
   split out of the .c because the unity build delivered it via include order */

#if defined(__x86_64__) || defined(_M_X64)
#include <immintrin.h>
#endif

#if defined(_WIN32) || defined(_WIN64)
    #define WIN32_LEAN_AND_MEAN
    #include <windows.h>
#else
    #include <sched.h>
    #include <unistd.h>
#endif

#include <pthread.h>
#include <stdatomic.h>

#undef LOAD
#undef STORE

#define L_R(v, ...)   atomic_load_explicit(&(v), memory_order_relaxed)
#define L(v)          atomic_load_explicit(&(v), memory_order_acquire)
#define S_R(v, x)     atomic_store_explicit(&(v), (x), memory_order_relaxed)
#define S(v, x)       atomic_store_explicit(&(v), (x), memory_order_release)
#define E_R(v, x)     atomic_exchange_explicit(&(v), (x), memory_order_relaxed)
#define E_A(v, x)     atomic_exchange_explicit(&(v), (x), memory_order_acquire)
#define FO(v, x)      atomic_fetch_or_explicit(&(v), (x), memory_order_release)
#define FA(v, x)      atomic_fetch_and_explicit(&(v), (x), memory_order_release)
#define CWX(v, e, d)  atomic_compare_exchange_weak_explicit(&(v), &(e), (d), \
                          memory_order_release, memory_order_relaxed)
#define CXS(v, e, d)  atomic_compare_exchange_strong_explicit(&(v), &(e), (d), \
                          memory_order_acquire, memory_order_relaxed)
#define TAS(v)        atomic_flag_test_and_set_explicit(&(v), memory_order_acquire)
#define CLR(v)        atomic_flag_clear_explicit(&(v), memory_order_release)

#if defined(_WIN32) || defined(_WIN64)
    #define SLEEP_MS(ms) Sleep(ms)
    #define EXPORT __declspec(dllexport)
#else
    #define SLEEP_MS(ms) usleep((ms) * 1000)
    #define EXPORT __attribute__((visibility("default")))
#endif

typedef pthread_t vmath_thread_t;
#define THREAD_FUNC        void*
#define THREAD_RETURN_VAL  NULL
