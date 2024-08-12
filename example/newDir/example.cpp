void bar(int**p, int** q) {
    int *t1 = *p;
    int *t2 = *q;
    *p = t1;
    *q = t2;
}

void foo() {
    int a, b;
    int *x = &a;
    int *y = &b;
    bar(&x, &y);
}