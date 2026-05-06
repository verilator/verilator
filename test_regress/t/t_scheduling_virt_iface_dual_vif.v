// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test: VIF member written through two different virtual
// interface handles pointing to the same underlying interface instance.
// The conditional trigger must detect value changes correctly regardless
// of which virtual handle performs the write.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

interface SimpleIf;
  logic [7:0] data;
endinterface

module t;
  logic clk = 0;
  int cyc = 0;

  SimpleIf intf();

  // Two different virtual interface handles to the same interface
  virtual SimpleIf vi1 = intf;
  virtual SimpleIf vi2 = intf;
  virtual SimpleIf vi_rd = intf;

  // Write through first virtual handle on odd cycles, second on even
  always @(posedge clk) begin
    if (cyc == 1) vi1.data <= 8'hAA;
    if (cyc == 2) vi2.data <= 8'hBB;
    if (cyc == 3) vi1.data <= 8'hCC;
    if (cyc == 4) vi2.data <= 8'hDD;
  end

  // Combinational logic reading through yet another virtual handle
  logic [7:0] observed;
  assign observed = vi_rd.data;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2: `checkh(observed, 8'hAA);
      3: `checkh(observed, 8'hBB);
      4: `checkh(observed, 8'hCC);
      5: `checkh(observed, 8'hDD);
      6: begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    endcase
  end

  initial begin
    repeat (20) #5 clk = ~clk;
  end
endmodule
