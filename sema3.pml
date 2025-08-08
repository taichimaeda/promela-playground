// semaphore with LIFO enqueue support
typedef Sema {
#ifndef SEMA_INIT
#define SEMA_INIT 0
#endif
  byte value = SEMA_INIT;
  bool waiting[NUM_THREADS];
  byte waiters[NUM_THREADS + 1];
  byte head;
  byte tail;
  byte count;
}

typedef Mutex {
  Sema sema;
  byte state;
}

Mutex mutex;

inline mutex_sema_acquire(lifo) {
  atomic {
    if
    :: mutex.sema.value > 0;
    :: else ->
       if
       :: lifo -> 
          mutex.sema.head = (mutex.sema.head + NUM_THREADS - 1) % NUM_THREADS;
          mutex.sema.waiters[mutex.sema.head] = _pid;
       :: else ->
          mutex.sema.waiters[mutex.sema.tail] = _pid;
          mutex.sema.tail = (mutex.sema.tail + 1) % NUM_THREADS;
       fi
       mutex.sema.count++;
       mutex.sema.waiting[_pid] = true;
       !mutex.sema.waiting[_pid]; // wait until ready
    fi
    mutex.sema.value--;
  }
}

inline mutex_sema_release() {
  atomic {
    if
    :: mutex.sema.count > 0 ->
       byte id = mutex.sema.waiters[mutex.sema.head];
       mutex.sema.head = (mutex.sema.head + 1) % NUM_THREADS;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--;
    :: else
    fi
    mutex.sema.value++;
  }
}