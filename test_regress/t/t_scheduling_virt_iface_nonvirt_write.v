// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test: VIF member written through both a virtual interface and
// a non-virtual (plain) interface reference. The conditional trigger must
// detect value changes correctly even when the member is updated through
// the non-virtual path.
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
  virtual SimpleIf vi = intf;

  // Write through virtual interface
  always @(posedge clk) begin
    if (cyc == 1) vi.data <= 8'hAA;
    if (cyc == 3) vi.data <= 8'hBB;
  end

  // Write through non-virtual (plain) interface
  always @(posedge clk) begin
    if (cyc == 2) intf.data <= 8'hCC;
    if (cyc == 4) intf.data <= 8'hDD;
  end

  // Combinational logic reading through virtual interface
  logic [7:0] observed;
  assign observed = vi.data;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      2: `checkh(observed, 8'hAA);
      3: `checkh(observed, 8'hCC);
      4: `checkh(observed, 8'hBB);
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
