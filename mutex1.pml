#define NUM_THREADS 3
#define MAX_SPIN 4

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

#define SEMA_INIT 1
#include "sema2.pml"
#include "atomic.pml"

Sema mutex_sema;

inline mutex_lock() {
  sema_acquire(mutex_sema);
}

inline mutex_unlock() {
  sema_release(mutex_sema);
}

byte num_threads_in_cs;
bool want_lock[NUM_THREADS];
bool have_lock[NUM_THREADS];

active [NUM_THREADS] proctype Thread() {
  assert(_pid < NUM_THREADS);
  do 
  :: want_lock[_pid] = true;
     mutex_lock();
     want_lock[_pid] = false;
     have_lock[_pid] = true;
     num_threads_in_cs++;
     num_threads_in_cs--;
     have_lock[_pid] = false;
     mutex_unlock();
  :: break;
  od
}

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }

// // no starvation
// ltl liveness {
//   [](want_lock[0] -> <>have_lock[0]) && 
//   [](want_lock[1] -> <>have_lock[1]) && 
//   [](want_lock[2] -> <>have_lock[2])
// }
