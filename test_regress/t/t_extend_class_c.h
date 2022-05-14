// -*- mode: C++; c-file-style: "cc-mode" -*-
//
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2006-2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class t_extend_class_c {
public:
    // CONSTRUCTORS
    t_extend_class_c() = default;
    ~t_extend_class_c() = default;
    // METHODS
    // This function will be called from a instance created in Verilog
    inline uint32_t my_math(uint32_t in) { return in + 1; }
};
