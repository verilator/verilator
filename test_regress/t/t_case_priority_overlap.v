// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Regression: a `priority` case item whose later condition (INST_B) is fully
// subsumed by an earlier condition (INST_A) of the *same* item. Overlap within
// a single case item is legal, but this previously crashed V3Case with a null
// pointer dereference: the priority "case item ignored" CASEOVERLAP diagnostic
// dereferenced 'overlappedCondp', which is null when the only covering item is
// the item itself. Must compile cleanly and simulate correctly.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  logic clk = 1'b0;
  always #5 clk = ~clk;

  logic [1:0] in;
  logic [1:0] out;

  always_comb begin
    priority casez (in)
      2'b1?,  // fully subsumes 2'b11 below on the same case clause
      2'b11:
      out = 2'b10;
      2'b0?: out = 2'b01;
    endcase
  end

  initial begin
    in = 2'b00;
    @(posedge clk);
    `checkh(out, 2'b01);

    in = 2'b01;
    @(posedge clk);
    `checkh(out, 2'b01);

    in = 2'b10;
    @(posedge clk);
    `checkh(out, 2'b10);

    in = 2'b11;
    @(posedge clk);
    `checkh(out, 2'b10);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
