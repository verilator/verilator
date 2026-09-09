// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module top_module;
  reg     [7:0] in1a, in2a, in1b, in2b;
  logic   [7:0] outa, outb;

  int logfile;

  module_a a1 (.in1(in1a), .in2(in2a), .out(outa));
  module_a a2 (.in1(in1b), .in2(in2b), .out(outb));

  initial begin
    // Initial values
    in1a = 0; in2a = 0; in1b = 0; in2b = 0;

    // t < 20
    repeat (20) begin
      in1a = 5;
      in2a = 10;
      in1b = 20;
      in2b = 30;
      #1;
      $display("$[%0t| outa: %0d | outb: %0d]", $time, outa, outb);
    end

    // 20 <= t < 63
    repeat (43) begin
      in1a = 0;
      in2a = 5;
      in1b = 15;
      in2b = 25;
      #1;
      $display("$[%0t| outa: %0d | outb: %0d]", $time, outa, outb);
    end

    // 63 <= t <= 78 -> no changes
    repeat (15) begin
      #1;
      $display("$[%0t| outa: %0d | outb: %0d]", $time, outa, outb);
    end

    // t > 78
    repeat (22) begin
      in1a = 10;
      in2a = 15;
      in1b = 25;
      in2b = 35;
      #1;
      $display("$[%0t| outa: %0d | outb: %0d]", $time, outa, outb);
    end

    $display("*-* All Finished *-*");
    $finish;
  end
endmodule

module module_a(
  input logic [7:0] in1,
  input logic [7:0] in2,
  output logic [7:0] out
);
  module_b b1 (.in1(in1), .in2(in2), .out(out));
endmodule

module module_b (
  input logic [7:0] in1,
  input logic [7:0] in2,
  output logic [7:0] out
);
  reg [127:0] bigRegister;
  always_comb begin
    out = in1 + in2;
  end
endmodule
