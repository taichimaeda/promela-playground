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
#define MUTEX_LOCKED 1
#define MUTEX_WAITER_SHIFT 2

inline mutex_lock() {
  byte iter;
  byte old;
  byte new;
  byte swapped;

  atomic_compare_and_swap(mutex.state, 0, MUTEX_LOCKED, swapped)
  if
  :: swapped -> goto done
  :: else
  fi

  iter = 0;
  old = mutex.state;
continue:
  do
  :: if
     :: old&MUTEX_LOCKED != 0 && iter < MAX_SPIN ->
        iter++;
        old = mutex.state;
        goto continue;
     :: else
     fi
     new = old | MUTEX_LOCKED;
     if
     :: old&MUTEX_LOCKED != 0 ->
        new = new + (1 << MUTEX_WAITER_SHIFT);
     :: else
     fi
     atomic_compare_and_swap(mutex.state, old, new, swapped);
     if
     :: swapped ->
        if
        :: old&MUTEX_LOCKED == 0 -> break
        :: mutex_sema_acquire();
           iter = 0
        fi
     :: else
     fi
     old = mutex.state
  od
done:
}

inline mutex_unlock() {
  byte old;
  byte new;
  byte swapped;

  atomic_add(mutex.state, -MUTEX_LOCKED, new);
  if
  :: new == 0; goto done
  :: else
  fi

  old = new;
  do
  :: if
     :: old>>MUTEX_WAITER_SHIFT == 0 || old&MUTEX_LOCKED == 0 ->
        goto done
     :: else
     fi
     new = old - 1<<MUTEX_WAITER_SHIFT;
     atomic_compare_and_swap(mutex.state, old, new, swapped);
     if
     :: swapped -> mutex_sema_acquire()
     :: else
     fi
     old = mutex.state
  od
done:
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

// // mutual exclusion
// ltl safety {
//   [](num_threads_in_cs <= 1)
// }

// no starvation (does not hold)
// ltl liveness {
//   [](want_lock[0] -> <>have_lock[0]) && 
//   [](want_lock[1] -> <>have_lock[1])
// }
