// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef int int_t;
  typedef enum int_t {INTT_VAL = 1} intt_e;
  intt_e intte;

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
