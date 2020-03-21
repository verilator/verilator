// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE

VM_PREFIX* tb = NULL;
bool pass = true;

double sc_time_stamp() { return 0; }

void check(const char* bus, int got, int exp) {
    if (got != exp) {
        VL_PRINTF("%%Error: Data mismatch on '%s', got=%x, exp=%x\n", bus, got, exp);
        pass = false;
    }
}

#ifdef SYSTEMC_VERSION
int sc_main(int, char**)
#else
int main()
#endif
{
    Verilated::debug(0);
    tb = new VM_PREFIX("tb");

#ifdef SYSTEMC_VERSION
    sc_signal<vluint32_t> i3;
    sc_signal<vluint32_t> o3;
    sc_signal<vluint32_t> i34[4];
    sc_signal<vluint32_t> o34[4];
    sc_signal<vluint32_t> i345[4][5];
    sc_signal<vluint32_t> o345[4][5];

    tb->i3(i3);
    tb->o3(o3);
    for (int i = 0; i < 4; i++) {
        tb->i34[i](i34[i]);
        tb->o34[i](o34[i]);
        for (int j = 0; j < 5; j++) {
            tb->i345[i][j](i345[i][j]);
            tb->o345[i][j](o345[i][j]);
        }
    }
#endif

    // loop through every possibility and check the result
#ifdef SYSTEMC_VERSION
    sc_start(1, SC_NS);
#  define ASSIGN(s,v) s.write(v)
#  define READ(s) s.read()
#else
    tb->eval();
#  define ASSIGN(s,v) tb->s = (v)
#  define READ(s) tb->s
#endif

    ASSIGN(i3, 13);
    for (int i = 0; i < 4; i++) {
        ASSIGN(i34[i], i);
        for (int j = 0; j < 5; j++) {
            ASSIGN(i345[i][j], i * 8 + j);
        }
    }

#ifdef SYSTEMC_VERSION
    sc_start(1, SC_NS);
#else
    tb->eval();
#endif

    check("o3", READ(o3), 13);
    for (int i = 0; i < 4; i++) {
        check("o34", READ(o34[i]), i);
        for (int j = 0; j < 5; j++) {
            check("o345", READ(o345[i][j]), i * 8 + j);
        }
    }

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from test\n");
    }
    return 0;
}
