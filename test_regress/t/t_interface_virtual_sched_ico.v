// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface If;
  logic [31:0] inc;
endinterface

module top (
    clk,
    inc1,
    inc2
);

  input clk;
  input [31:0] inc1;
  input [31:0] inc2;
  int cyc = 0;

  If intf1();
  If intf2();
  virtual If vif1 = intf1;
  virtual If vif2 = intf2;

  assign vif1.inc  = inc1;
  assign intf2.inc = inc2;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc >= 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always_comb $write("[%0t] intf1.inc==%0h\n", $time, intf1.inc);
  always_comb $write("[%0t] vif2.inc==%0h\n", $time, vif2.inc);

endmodule
