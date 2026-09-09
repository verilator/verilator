// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets inside generate loops (instance, unpacked struct, interfaces)

typedef struct {
  logic [7:0] x;
  logic [7:0] y;
} pair_t;

interface simple_if;
  logic [7:0] data;
endinterface

module leaf(input logic [7:0] i, output logic [7:0] o);
  logic [7:0] mid;
  assign mid = i + 8'h01;
  assign o = mid;
endmodule

module producer(simple_if b, input logic [7:0] val);
  always_comb b.data = val;
endmodule

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] q [2];
  logic [7:0] iv = 8'h10;
  logic [7:0] plain;
  logic [7:0] arrayed;

  // A module instantiated inside a generate block is reached through the block
  // scope: "top_module.lane[0].u.mid". The unrolled iterations share one module,
  // so which instance is faulted is selected at run time by the bound path.
  genvar g;
  generate
    for (g = 0; g < 2; g = g + 1) begin : lane
      leaf u (.i(8'h10 + g[7:0]), .o(q[g]));
    end
  endgenerate

  // Whole unpacked struct per iteration. Both are targets, only lagg[1].gp is bound
  for (genvar k = 0; k < 2; k++) begin : lagg
    pair_t gp;
    always @(posedge clk) begin
      gp.x <= 8'h10 + 8'(k * 8) + cyc[7:0];
      gp.y <= 8'h50 + 8'(k * 8) + cyc[7:0];
    end
  end

  // Interfaces per iteration (instance (lif[0].bi), element of an array (lif[1].barr[1]))
  for (genvar m = 0; m < 2; m++) begin : lif
    simple_if bi ();
    simple_if barr[2] ();
    producer p (.b(bi), .val(iv + m[7:0]));
    producer pa0 (.b(barr[0]), .val(iv + 8'h20));
    producer pa1 (.b(barr[1]), .val(iv + 8'h30));
  end
  assign plain = lif[0].bi.data;
  assign arrayed = lif[1].barr[1].data;

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    $display("$[%0d| q0: %02x q1: %02x]", cyc, q[0], q[1]);
    $display("[%0d] lane0=%02x %02x lane1=%02x %02x", cyc, lagg[0].gp.x, lagg[0].gp.y,
             lagg[1].gp.x, lagg[1].gp.y);
    $display("[%0d] plain=%02x arrayed=%02x", cyc, plain, arrayed);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
