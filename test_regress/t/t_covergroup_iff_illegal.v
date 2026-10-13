// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while (0);
// verilog_format: on

module t;
  int sample_value;

  covergroup cg with function sample (bit [2:0] value, bit point_enable, bit bin_enable);
    cp: coverpoint value iff (point_enable) {
      bins good = {4};
      illegal_bins scalar = {5} iff (bin_enable);
      illegal_bins values[] = {0, 1} iff (bin_enable);
      wildcard illegal_bins wild = {3'b11?} iff (bin_enable);
    }
  endgroup

  cg inst = new;

  initial begin
    if (!$value$plusargs("value=%d", sample_value)) `stop;
    for (int i = 0; i < 8; ++i) inst.sample(3'(i), 1, 0);
    for (int i = 0; i < 8; ++i) inst.sample(3'(i), 0, 1);
`ifdef VERILATOR
    `checkd($c32("Verilated::threadContextp()->errorCount()"), 0);
`endif
    $display("Disabled guards produced no illegal-bin errors.");
    inst.sample(3'(sample_value), 1, 1);
    $finish;
  end
endmodule
