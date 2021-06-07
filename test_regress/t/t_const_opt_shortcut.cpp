#include <iostream>
extern "C" int import_func0() {
    static int c = 0;
    return ++c;
}

extern "C" int import_func1() {
    static int c = 0;
    return ++c;
}
extern "C" int import_func2() {
    static int c = 0;
    return ++c;
}

extern "C" int import_func3() {
    static int c = 0;
    return ++c;
}
extern "C" int import_func4() {
    static int c = 0;
    return ++c;
}
