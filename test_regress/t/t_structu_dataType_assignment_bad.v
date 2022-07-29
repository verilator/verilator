// DESCRIPTION: Verilator: Verilog Test module for specialized type default values
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Mostafa Gamal.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off UNPACKED */

module top();


  typedef struct { // IEEE 1800-2017 SV CH:10.9.2
    int A;
    struct {
    int B, C;
    } BC1, BC2;
  } DEF_struct;

  DEF_struct DEF_bad = '{1: 5, default: 10};

endmodule
