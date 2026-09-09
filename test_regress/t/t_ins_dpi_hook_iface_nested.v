// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Signals of interfaces nested in an interface (ob.in.data, ob.arr[1].data) and of the outer
// interface itself (ob.sum)
interface inner_if;
  logic [7:0] other;
  logic [7:0] data;
endinterface

interface outer_if;
  logic [7:0] sum;
  inner_if in ();
  inner_if arr[2] ();
  assign sum = in.data + 8'h01;
endinterface

module mid (
    input logic [7:0] val,
    output logic [7:0] q,
    output logic [7:0] r,
    output logic [7:0] s
);
  outer_if ob ();
  assign ob.in.other = 8'h00;
  assign ob.in.data = val;
  assign ob.arr[0].other = 8'h00;
  assign ob.arr[0].data = 8'h00;
  assign ob.arr[1].other = 8'h00;
  assign ob.arr[1].data = val ^ 8'h80;
  assign q = ob.in.data;
  assign r = ob.arr[1].data;
  assign s = ob.sum;
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] val;
  logic [7:0] q, r, s;

  assign val = 8'h20 + cyc[7:0];
  mid m (
      .val(val),
      .q(q),
      .r(r),
      .s(s)
  );

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("$[%0d| q: %02x r: %02x s: %02x]", cyc, q, r, s);
    if (cyc >= 7) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
