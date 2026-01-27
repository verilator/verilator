// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 George Polack
// SPDX-License-Identifier: CC0-1.0

#include VM_PREFIX_INCLUDE
#include <cmath>
#include <limits>

using namespace sc_core;
using namespace sc_dt;

VM_PREFIX* tb = nullptr;
bool pass = true;

double sc_time_stamp() { return 0; }

void compareDoubles(double const lwp, double const rwp,
                    double epsilon = std::numeric_limits<double>::epsilon()) {
    auto diff = std::fabs(lwp - rwp);
    if (diff >= epsilon) {
        pass &= false;
        VL_PRINTF("%%Error: There is a difference of %f, in double variables\n", diff);
    }
}

#ifdef SYSTEMC_VERSION
int sc_main(int, char**)
#else
int main()
#endif
{
    Verilated::debug(0);
    tb = new VM_PREFIX{"tb"};

    double input_var = 1.5;
    double out_var;

#ifdef SYSTEMC_VERSION
    // clang-format off
    sc_signal<double> SC_NAMED(i_a), SC_NAMED(o_z);

    tb->i_a(i_a); tb->o_z(o_z);
    // clang-format on
#endif

#ifdef SYSTEMC_VERSION
    sc_start(1, SC_NS);
#else
    tb->eval();
#endif

    // This testcase is testing conversion to/from Verilog real to/from SystemC double.
    VL_ASSIGN_SDD(0, i_a, input_var);

#ifdef SYSTEMC_VERSION
    sc_start(1, SC_NS);
#else
    tb->eval();
#endif

    VL_ASSIGN_DSD(0, out_var, o_z);

    compareDoubles(input_var, out_var);

    tb->final();
    VL_DO_DANGLING(delete tb, tb);

    if (pass) {
        VL_PRINTF("*-* All Finished *-*\n");
    } else {
        vl_fatal(__FILE__, __LINE__, "top", "Unexpected results from test\n");
    }
    return 0;
}
