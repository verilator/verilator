// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

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
