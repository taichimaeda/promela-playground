#ifndef NUM_THREADS
#define NUM_THREADS 2 // default value if not set by -DNUMTHREADS
#endif

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
  d_step { loc = (loc == expected -> desired : loc); ret = (loc == desired) }
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

#define MUTEX_LOCKED 1

Mutex mutex;

inline mutex_sema_acquire() {
  atomic {
    if
    :: mutex.sema.value > 0 -> mutex.sema.value--
    :: else ->
       mutex.sema.waiters ! _pid;
       mutex.sema.waiting[_pid] = true;
       mutex.sema.count++
    fi
  }
  !mutex.sema.waiting[_pid] // wait until ready
}

inline mutex_sema_release() {
  atomic {
    if
    :: mutex.sema.count == 0 -> mutex.sema.value++
    :: else -> 
       byte id;
       mutex.sema.waiters ? id;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--
    fi
  }
}

#define MAX_SPIN 4

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
  od
}

// mutual exclusion
ltl safety {
  [](num_threads_in_cs <= 1)
}

// no starvation (does not hold)
// ltl liveness {
//   [](want_lock[0] -> <>have_lock[0]) && 
//   [](want_lock[1] -> <>have_lock[1])
// }
