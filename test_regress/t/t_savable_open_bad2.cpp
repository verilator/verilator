// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

#include <iostream>

#include <verilated.h>
#include <verilated_save.h>
#include VM_PREFIX_INCLUDE

#include "TestCheck.h"

//======================================================================

unsigned int main_time = 0;
int errors = 0;

double sc_time_stamp() { return main_time; }

int main(int argc, char* argv[]) {
    // No need to make a model:  topp = new VM_PREFIX;

    Verilated::debug(0);
    {
        VerilatedSave os;
        os.open("/No_such_file_as_this");
        TEST_CHECK_EQ(os.isOpen(), false);
    }
    {
        VerilatedRestore os;
        os.open("/No_such_file_as_this");
        TEST_CHECK_EQ(os.isOpen(), false);
    }

    return errors ? 10 : 0;
}
