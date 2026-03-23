// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

function int get_trace_level;
   return 1;
endfunction

function void varsdump;
   $dumpvars(get_trace_level());
endfunction

function void setup_trace;
  $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
  varsdump();
endfunction

module t(
    input clk
);
  int cyc;

  sub #(10) sub_a(.*);
  sub #(20) sub_b(.*);

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 5) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

module sub #(
    parameter int ADD
)(
    input int cyc
);
  int value;
  always_comb value = cyc + ADD;

  initial begin
    setup_trace;
  end

  deep #(ADD + 1) deep_i(.*);
endmodule

module deep #(
    parameter int ADD
)(
    input int cyc
);
  int inner;
  always_comb inner = cyc + ADD;
endmodule
