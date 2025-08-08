# PromelaPlayground

Spin Version 6.5.2 -- 6 December 2019

```console
spin -a version1.pml
clang -o pan pan.c
```

```console
./pan -a -b
./pan -a -b -N "safety"
./pan -a -b -N "liveness"
```

```console
./pan -a -b
spin -p -t version1.pml
```

Checking for deadlocks:

* Comment out LTL formulas to check for invalid end states
* Run `spin -a version1.pml && clang -o pan pan.c && ./pan -a -b`

Checking mutual exclusion property (safety):

* Run `spin -a version1.pml && clang -o pan pan.c && ./pan -a -b -N "safety"`

Checking no starvation property (liveness):

* Run `spin -a version1.pml && clang -o pan pan.c && ./pan -a -b -f -N "liveness"`
