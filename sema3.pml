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

inline sema_acquire(sema, lifo) {
  atomic {
    do
    :: sema.value == 0 ->
       if
       :: lifo -> 
          sema.head = (sema.head + NUM_THREADS - 1) % NUM_THREADS;
          sema.waiters[sema.head] = _pid;
       :: else ->
          sema.waiters[sema.tail] = _pid;
          sema.tail = (sema.tail + 1) % NUM_THREADS;
       fi
       sema.count++;
       sema.waiting[_pid] = true;
       !sema.waiting[_pid]; // wait until ready
    :: else -> break
    od
    assert(sema.value > 0);
    sema.value--;
  }
}

inline sema_release(sema) {
  atomic {
#ifndef MAX_SEMA_VALUE
  sema.value++;
#else
  if
  :: sema.value < MAX_SEMA_VALUE ->
     sema.value++;
  :: else
  fi
#endif
    if
    :: sema.count > 0 ->
       byte id = sema.waiters[sema.head];
       sema.head = (sema.head + 1) % NUM_THREADS;
       sema.waiting[id] = false;
       sema.count--;
    :: else
    fi
  }
}