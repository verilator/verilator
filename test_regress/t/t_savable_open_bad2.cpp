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

//======================================================================

#define CHECK_RESULT_HEX(got, exp) \
    do { \
        if ((got) != (exp)) { \
            std::cout << std::dec << "%Error: " << __FILE__ << ":" << __LINE__ << std::hex \
                      << ": GOT=" << (got) << "   EXP=" << (exp) << std::endl; \
            exit(10); \
        } \
    } while (0)

//======================================================================

unsigned int main_time = 0;

double sc_time_stamp() { return main_time; }

int main(int argc, char* argv[]) {
    // No need to make a model:  topp = new VM_PREFIX;

    Verilated::debug(0);
    {
        VerilatedSave os;
        os.open("/No_such_file_as_this");
        CHECK_RESULT_HEX(os.isOpen(), false);
    }
    {
        VerilatedRestore os;
        os.open("/No_such_file_as_this");
        CHECK_RESULT_HEX(os.isOpen(), false);
    }

    exit(0);
}
