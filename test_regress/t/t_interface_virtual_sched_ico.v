// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface If;
  logic [31:0] inc;
endinterface

module top;

  logic clk = 0;
  logic [31:0] inc1 = 0;
  logic [31:0] inc2 = 0;
  int cyc = 0;

  If intf1();
  If intf2();
  virtual If vif1 = intf1;
  virtual If vif2 = intf2;

  // assign vif1.inc  = inc1;
  always @(posedge clk) begin
    vif1.inc <= inc1;
  end
  assign intf2.inc = inc2;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc >= 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  always @(intf1.inc) begin
    $write("[%0t] intf1.inc==%h\n", $time, intf1.inc);
  end
  always @(vif2.inc) begin
    $write("[%0t] vif2.inc==%h\n", $time, vif2.inc);
  end

  initial begin
    repeat (30) #5ns clk = ~clk;
  end

  initial begin
    inc1 = 1;
    inc2 = 1;

    repeat (10) begin
      #10ns;
      inc1 = inc1 + 1;
      inc2 = inc2 + 1;
    end

  end

endmodule
