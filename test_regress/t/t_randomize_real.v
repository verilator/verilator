// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Cls;
  rand real m_real;
endclass

module test;
  localparam LOOPS = 1000;

  int negative;
  int bitcounts[64];
  int i;
  bit [63:0] rbits;

  initial begin
    Cls c;
    c = new;

    repeat (LOOPS) begin
      i = c.randomize();
      `checkd(i, 1);

      rbits = $realtobits(c.m_real);
`ifdef TEST_VERBOSE
      $display("%x %g", rbits, c.m_real);
`endif

      if (c.m_real < 0) negative++;
      for (int b = 0; b < 64; ++b) begin
        if (rbits[b]) bitcounts[b]++;
      end
    end

    if (negative < LOOPS * 0.4) $error("Too few negative %0d", negative);
    for (int b = 0; b < 64; ++b) begin
      if (bitcounts[b] < LOOPS * 0.4) $error("Too few 1 bits at [%0d]: %0d", b, bitcounts[b]);
    end
    $finish;
  end

endmodule
