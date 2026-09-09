// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Targets here are aggregates e.g. a 2-D array and an array of structs, hooked as a whole and
// read through non-constant indices, a struct holding a packed struct, and an element read
// through an index with a side effect (rf[nexti()])
typedef struct packed {
  logic [3:0] hi;
  logic [3:0] lo;
} nib_t;
typedef struct {
  nib_t       n;
  logic [7:0] z;
} mix_t;
typedef struct {
  logic [7:0] x;
  logic [7:0] y;
} pt;

module top_module;
  logic clk = 0;
  int cyc = 0;
  logic [7:0] m2[2][3];
  mix_t mx = '{n: 8'h00, z: 8'h00};
  logic [7:0] rf[4];
  pt aos[2];
  int calls = 0;
  logic i;
  logic [1:0] j;
  logic [1:0] idx;
  logic [7:0] rd;

  function automatic int nexti();
    calls++;
    return 2;
  endfunction

  initial for (int a = 0; a < 2; a++) for (int b = 0; b < 3; b++) m2[a][b] = 8'(16 * a + b);
  initial for (int a = 0; a < 4; a++) rf[a] = 8'(8'h40 + a);
  initial begin
    aos[0].x = 8'h0a;
    aos[0].y = 8'h0b;
    aos[1].x = 8'h1a;
    aos[1].y = 8'h1b;
    idx = 2'd0;
  end

  assign i = cyc[0];
  assign j = 2'(cyc % 3);

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    mx.n <= {cyc[3:0], 4'h5};
    mx.z <= 8'h60 + cyc[7:0];
    idx <= idx + 2'd1;
    rd <= aos[idx[0]].y;
    $display("$[%0d| m2[%0d][%0d]: %02x mx: %02x %02x rf[2]: %02x %02x]", cyc, i, j, m2[i][j],
             mx.n, mx.z, rf[2], rf[nexti()]);
    $display("$[%0d| idx: %0d rd: %02x a1y: %02x a0x: %02x]", cyc, idx, rd, aos[1].y, aos[0].x);
    if (cyc > 6) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule
