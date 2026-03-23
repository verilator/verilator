// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 by Marco Bartoli.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

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

  function void dump_from_func;
    $dumpvars(1, t);
  endfunction

  task setup_trace;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    dump_from_func();
  endtask

  deep #(ADD + 1) deep_i(.*);

  initial begin
    setup_trace();
  end
endmodule

module deep #(
    parameter int ADD
)(
    input int cyc
);
  int inner;
  int t;
  always_comb inner = cyc + ADD;

  function void dump_from_func;
    $dumpvars(1, t);
  endfunction

  task setup_trace;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    dump_from_func();
  endtask

  initial begin
    setup_trace();
  end
endmodule
