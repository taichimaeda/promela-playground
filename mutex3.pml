#ifndef NUM_THREADS
#define NUM_THREADS 2 // default value if not set by -DNUMTHREADS
#endif

#define MAX_SPIN 4

#define MUTEX_LOCKED 1       // 1 << 0
#define MUTEX_WOKEN 2        // 1 << 1
#define MUTEX_STARVING 4     // 1 << 2
#define MUTEX_WAITER_SHIFT 3 // 3

inline atomic_load(loc, ret) {
  d_step { ret = loc }
}

inline atomic_store(loc, val) {
  d_step { loc = val }
}

inline atomic_swap(loc, val, ret) {
  d_step { ret = loc; loc = val }
}

inline atomic_compare_and_swap(loc, expected, desired, ret) {
  d_step { ret = (loc == expected); loc = (ret -> desired : loc) }
}

inline atomic_add(loc, val, ret) {
  d_step { loc = loc + val; ret = loc }
}

typedef Sema {
  byte value;
  bool waiting[NUM_THREADS];
  chan waiters = [NUM_THREADS] of { byte };
  byte count;
}

typedef Mutex {
  Sema sema;
  byte state;
}

Mutex mutex;

inline mutex_sema_acquire() {
  atomic {
    if
    :: mutex.sema.value == 0 ->
       mutex.sema.waiters ! _pid;
       mutex.sema.waiting[_pid] = true;
       mutex.sema.count++
    :: else
    fi
    !mutex.sema.waiting[_pid]; // wait until ready
    mutex.sema.value--
  }
}

inline mutex_sema_release() {
  atomic {
    if
    :: mutex.sema.count > 0 ->
       byte id;
       mutex.sema.waiters ? id;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--
    :: else
    fi
    mutex.sema.value++;
  }
}

inline mutex_sema_wakeup() {
  atomic {
    if
    :: mutex.sema.count > 0 ->
       byte id;
       mutex.sema.waiters ? id;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--;
       mutex.sema.value++ // only if there are waiters
    :: else
    fi
  }
}

inline mutex_lock() {
  byte old;
  byte iter = 0;
continue:
  do
  :: atomic_swap(mutex.state, MUTEX_LOCKED, old);
     if
     :: old != 0 ->
        if
        :: iter < MAX_SPIN ->
           iter++;
           goto continue;
        :: else
        fi
        mutex_sema_acquire()
     :: else -> break
     fi
  od
}

inline mutex_unlock() {
  atomic_store(mutex.state, 0);
  mutex_sema_release()
}

byte num_threads_in_cs;

active [NUM_THREADS] proctype Thread() {
  assert(_pid < NUM_THREADS);
  do 
  :: mutex_lock();
     num_threads_in_cs++;
     num_threads_in_cs--;
     mutex_unlock();
  :: break
  od
}

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }

// no starvation (does not hold)
// ltl liveness {
//   [](want_lock[0] -> <>have_lock[0]) && 
//   [](want_lock[1] -> <>have_lock[1])
// }
