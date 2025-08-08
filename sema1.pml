// semaphore with random wake up order
typedef Sema {
#ifndef SEMA_INIT
#define SEMA_INIT 0
#endif
  byte value = SEMA_INIT;
}

typedef Mutex {
  Sema sema;
  byte state;
}

Mutex mutex;

inline mutex_sema_acquire() {
  atomic { mutex.sema.value > 0 -> mutex.sema.value--; } 
}

inline mutex_sema_release() {
  atomic { mutex.sema.value++; }
}
