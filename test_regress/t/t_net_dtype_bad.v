// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls;
endclass

module t;
  typedef real real_t;

  typedef struct packed {
    bit m_bit;
  } bad_t;

  typedef struct {
    logic m_bit;
  } ok_unpk_t;

  typedef struct packed {
    logic m_bit;
  } ok_t;

  wire real_t bad_real;  // <--- Error - bad net type

  wire Cls bad_class;  // <--- Error - bad net type

  wire string bad_string;  // <--- Error - bad net type

  wire bit bad_bit;    // <--- Error - bad net type

  wire bad_t bad_struct;    // <--- Error - bad net type

  wire ok_unpk_t ok_unpk_struct;

  wire ok_t ok_struct;  // Ok

  initial $stop;
endmodule
