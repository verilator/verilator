// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Kristof Marien
// SPDX-License-Identifier: CC0-1.0

// A DUT input only reached by a clocking block output through a bound harness
// may be connected to an expression one level up. The expression cannot be
// driven back, so the port keeps its plain input connection.

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

/* verilator lint_off ASSIGNIN */
interface sender_if (
    input wire clk,
    input wire [7:0] bus
);
  clocking cb @(posedge clk);
    default input #1step output #1step;
    output bus;
  endclocking
endinterface
/* verilator lint_on ASSIGNIN */

interface harness_if (
    input wire clk,
    input wire [3:0] hi,
    input wire [3:0] lo
);
  sender_if sender (
      .clk(clk),
      .bus({hi, lo})
  );
endinterface

module dut (
    input wire clk,
    input wire [3:0] hi,
    input wire [3:0] lo,
    output logic [7:0] seen
);
  always_comb seen = {hi, lo};

  bind dut harness_if harness (.*);
endmodule

module t;
  logic clk = 1'b0;
  logic [3:0] a = 4'h3;
  logic [3:0] b = 4'h5;
  logic [7:0] seen;

  dut dut_i (
      .clk(clk),
      .hi(a & b),
      .lo(a | b),
      .seen(seen)
  );

  always #5 clk = ~clk;

  initial begin
    #1;
    `checkh(seen, 8'h17);
    `checkh(dut_i.harness.sender.bus, 8'h17);
    a = 4'hc;
    b = 4'h6;
    #1;
    `checkh(seen, 8'h4e);
    `checkh(dut_i.harness.sender.bus, 8'h4e);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
