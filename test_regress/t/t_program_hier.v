// DESCRIPTION: Verilator: Program scheduling with hierarchical blocks evaluated from Re-NBA
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module sub (
    input [6:0] d,
    output [6:0] q
);  /*verilator hier_block*/
  assign q = d + 7'd1;
endmodule

module t;
  bit clk;
  bit [6:0] d;
  wire [6:0] q;
  string order;
  always #5 clk = ~clk;
  // The drive commits in Re-NBA, which evaluates the hierarchical block
  clocking cb @(posedge clk);
    output #0 d;
  endclocking
  sub u (
      .d,
      .q
  );
  always @(q) begin
    if ($time != 0) begin
      #0 order = {order, "m"};
    end
  end
  p p ();
endmodule

program p;
  initial begin
    @(t.cb);
    t.cb.d <= 7'd5;
    @(t.q);
    `checkd(t.q, 6)
    t.order = {t.order, "p"};
    #0 t.order = {t.order, "P"};
    #1;
    `checks(t.order, "pPm")
    $write("*-* All Finished *-*\n");
    $finish;
  end
endprogram
