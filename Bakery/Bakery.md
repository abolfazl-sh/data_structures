```c
// Declaration and initial values of global variables
Entering: array [1..NUM_THREADS] of bool = {false};
Number:   array [1..NUM_THREADS] of integer = {0};

lock(integer i) {
    Entering[i] = true;
    Number[i] = 1 + max(Number[1], ..., Number[NUM_THREADS]);
    Entering[i] = false;

    for (integer j = 1; j <= NUM_THREADS; j++) {

        // Wait until thread j receives its number:
        while (Entering[j]) {
            /* nothing */
        }

        // Wait until all threads with smaller numbers or with the same
        // number, but with higher priority, finish their work:
        while ((Number[j] != 0) && ((Number[j], j) < (Number[i], i))) {
            /* nothing */
        }
    }
}

unlock(integer i) {
    Number[i] = 0;
}

Thread(integer i) {
    while (true) {
        lock(i);

        // The critical section goes here...

        unlock(i);

        // Non-critical section...
    }
}
```
