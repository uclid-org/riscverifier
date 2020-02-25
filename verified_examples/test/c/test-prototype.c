// TEST 1
int max_int(int x, int y) {
    if (x > y) {
        return x;
    } else {
        return y;
    }
}

// TEST 2
long max_long(long x, long y) {
    if (x > y) {
        return x;
    } else {
        return y;
    }
}

// TEST 3
int global_x;
int get_global_x() {
    return global_x;
}

int global_x_array[10];
int get_global_x_array(int i) {
    return global_x_array[i];
}



int main() {
    int a, b;
    long c, d;
    // TEST 1
    a = max_int(a, b);
    // TEST 2
    c = max_long(c, d);
    // TEST 3
    a = get_global_x();
    // TEST 4
    a = get_global_x_array(b);
    return 0;
}
