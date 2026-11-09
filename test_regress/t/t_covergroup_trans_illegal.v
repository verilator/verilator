// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test an illegal transition bin of a sequence long enough to be matched from a table

// verilog_format: off
`define SEQ8 0 => 1 => 0 => 1 => 0 => 1 => 0 => 1
`define SEQ64 `SEQ8 => `SEQ8 => `SEQ8 => `SEQ8 => `SEQ8 => `SEQ8 => `SEQ8 => `SEQ8
// verilog_format: on

module t;
  covergroup cg with function sample (bit [1:0] v);
    cp: coverpoint v {
      bins rise = (0 => 1);
      illegal_bins bad_long = (`SEQ64 => 2);  // 65 values
    }
  endgroup

  cg inst = new;

  initial begin
    for (int i = 0; i < 64; ++i) inst.sample(2'(i % 2));
    inst.sample(3);  // Not 2
    for (int i = 0; i < 64; ++i) inst.sample(2'(i % 2));
    $display("No illegal transition completed.");
    inst.sample(2);  // bad_long
    $finish;
  end
endmodule
