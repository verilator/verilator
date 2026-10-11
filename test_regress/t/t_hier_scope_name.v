// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  int cyc = 0;
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 9) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
  sub u_sub (.clk(clk), .cyc(cyc));
endmodule

`ifndef USE_LIB_SUB
module sub (
    input clk,
    input int cyc
);
  /*verilator hier_block*/
  task automatic show();
    $display("[%0d] sub task: %m", cyc);
  endtask
  always @(posedge clk) begin
    if (cyc == 1) $display("[%0d] sub: %m", cyc);
    if (cyc == 2) begin : blk
      $display("[%0d] sub begin: %m", cyc);
    end
    if (cyc == 3) show();
  end
  leaf u_leaf (.clk(clk), .cyc(cyc));
endmodule
`endif

`ifndef USE_LIB_LEAF
module leaf (
    input clk,
    input int cyc
);
  /*verilator hier_block*/
  always @(posedge clk) begin
    if (cyc == 4) $display("[%0d] leaf: %m", cyc);
    if (cyc == 5) begin : blk
      $display("[%0d] leaf begin: %m", cyc);
    end
  end
endmodule
`endif
