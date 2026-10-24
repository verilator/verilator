// DESCRIPTION: Verilator: An NBA through a virtual interface whose handle the process also
// writes, after an NBA to the member: the NBA through the virtual interface is last
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface bus;
  logic [7:0] y;
endinterface

module t;
  bit clk;
  int cyc;
  always #5 clk = ~clk;

  bus f ();
  virtual bus vf;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    vf = f;
    f.y <= 8'(cyc);
    vf.y <= 8'hff;
  end

  always @(negedge clk) begin
    if (cyc >= 1) `checkd(f.y, 8'hff);
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
