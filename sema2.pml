// semaphore with FIFO wake up order
typedef Sema {
#ifndef SEMA_INIT
#define SEMA_INIT 0
#endif
  byte value = SEMA_INIT;
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
       mutex.sema.count++;
       mutex.sema.waiters ! _pid;
       mutex.sema.waiting[_pid] = true;
       !mutex.sema.waiting[_pid]; // wait until ready
    :: else
    fi
    mutex.sema.value--;
  }
}

inline mutex_sema_release() {
  atomic {
    if
    :: mutex.sema.count > 0 ->
       byte id;
       mutex.sema.waiters ? id;
       mutex.sema.waiting[id] = false;
       mutex.sema.count--;
    :: else
    fi
    mutex.sema.value++;
  }
}