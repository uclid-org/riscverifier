int gx;
long gy;
int gxa[10];

struct testA {
    long t;
};


struct testA as[10];

struct testS {
    int x;
    int y;
    int z;
    struct testA ss;
};

//struct testS ss[10];
int foo(struct testS s) {
    return s.x;
}

int bar(int i) {
    return gxa[i];
}

int bar2(int x[10]) {
    return 0;
}

long max2(long x, long y) {
    if (x > y) {
        return x;
    } else {
        return y;
    }
}

long max3(long x, long  y, long z) {
    int max_xy = max2(x, y);
    return max2(max_xy, z);
}

int main() {
    long z;
    z = max3(0, 10, 20);
    z = gy;
    struct testA a = { 10 };
    int k;
    k = gx;
    k = gxa[5];
    return 0;
}
