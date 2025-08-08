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

inline sema_acquire(sema) {
  atomic {
    if
    :: sema.value == 0 ->
       sema.count++;
       sema.waiters ! _pid;
       sema.waiting[_pid] = true;
       !sema.waiting[_pid]; // wait until ready
    :: else
    fi
    sema.value--;
  }
}

inline sema_release(sema) {
  atomic {
    if
    :: sema.count > 0 ->
       byte id;
       sema.waiters ? id;
       sema.waiting[id] = false;
       sema.count--;
    :: else
    fi
    sema.value++;
  }
}