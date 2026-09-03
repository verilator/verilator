// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 0;
  always #5 clk = ~clk;  // Posedges at 5, 15, 25, ...
  logic clk2 = 1;
  always #5 clk2 = ~clk2;  // Posedges at 10, 20, 30, ...
  logic a = 0;
  int fails_or = 0;
  int fails_c1 = 0;
  int fails_c2 = 0;
  int fails_or_rep = 0;
  int fails_edge_rep = 0;
  int fails_inst = 0;

  property p_not_a;
    !a;
  endproperty
  property p_or_inst;
    @(posedge clk or posedge clk2) p_not_a;
  endproperty

  PROP :
  assert property (@(posedge clk or posedge clk2) 1 == 1);

  ap_or :
  assert property (@(posedge clk or posedge clk2) a |-> !a)
  else fails_or = fails_or + 1;
  ap_c1 :
  assert property (@(posedge clk) a |-> !a)
  else fails_c1 = fails_c1 + 1;
  ap_c2 :
  assert property (@(posedge clk2) a |-> !a)
  else fails_c2 = fails_c2 + 1;

  // clk2 is ~clk, so both clocks tick at every edge of clk
  ap_or_rep :
  assert property (@(posedge clk or posedge clk2) a [= 2] |-> !a)
  else fails_or_rep = fails_or_rep + 1;
  ap_edge_rep :
  assert property (@(edge clk) a [= 2] |-> !a)
  else fails_edge_rep = fails_edge_rep + 1;

  ap_or_inst :
  assert property (p_or_inst)
  else fails_inst = fails_inst + 1;

  initial begin
    #4 a = 1;  // Covers clk posedges 5, 15, 25 and clk2 posedges 10, 20
    #22 a = 0;
    #10 $finish;
  end

  final begin
    `checkd(fails_or, fails_c1 + fails_c2);
    `checkd(fails_or, 5);
    `checkd(fails_or_rep, fails_edge_rep);
    `checkd(fails_inst, fails_or);
    $write("*-* All Finished *-*\n");
  end
endmodule
