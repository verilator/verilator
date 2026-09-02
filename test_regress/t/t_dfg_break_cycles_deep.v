// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Drew Risinger
// SPDX-License-Identifier: CC0-1.0

// A packed array driven one bit per generate iteration, and read back at a
// variable index. The many single bit drivers form a long Concat chain in the
// DFG, and the variable index read makes the graph cyclic at word
// granularity, so V3DfgBreakCycles must trace the drivers of the individual
// (acyclic) bits through the whole Concat chain.

module prim (
  input logic i,
  output logic o
  );
  assign o = !(!i);
endmodule

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;

  localparam WIDTH = 2;
  localparam DEPTH = 512;

  logic [WIDTH-1:0] din = '0;
  logic [WIDTH-1:0][$clog2(DEPTH+1)-1:0] sel = '0;
  logic [WIDTH-1:0] dout;

  // verilator lint_off UNOPTFLAT
  logic [WIDTH-1:0][DEPTH:0] arr;
  // verilator lint_on UNOPTFLAT

  generate
    for (genvar i = 0; i < WIDTH; ++i) begin : gen_width
      assign arr[i][0] = din[i];
      for (genvar j = 0; j < DEPTH; ++j) begin : gen_depth
        prim u_prim (.i(arr[i][j]), .o(arr[i][j+1]));
      end
    end
  endgenerate

  always_comb begin
    dout = '0;
    for (int i = 0; i < WIDTH; ++i) begin
      if (sel[i] <= DEPTH) dout[i] = arr[i][sel[i]];
    end
  end

  int cyc = 0;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    din <= WIDTH'(cyc);
    for (int i = 0; i < WIDTH; ++i) sel[i] <= $clog2(DEPTH+1)'((cyc * 7 + i) % (DEPTH + 1));
    // The chain is a buffer, so every element equals the driving input bit
    if (cyc > 1) begin
      if (dout !== din) begin
        $write("%%Error: dout=%0x din=%0x\n", dout, din);
        $stop;
      end
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
