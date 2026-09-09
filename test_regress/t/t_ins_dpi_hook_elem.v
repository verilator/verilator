// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked array targets: a whole array read through a non-constant index, an element read in
// its own module, and elements of an ascending and a descending range
module top_module;
  logic       clk = 0;
  int         cyc = 0;

  logic [7:0] mem [4];
  logic [1:0] addr;
  logic [7:0] rd;

  logic [7:0] a = 8'd10;
  logic [7:0] q;
  sub s (.a(a), .q(q));

  logic [7:0] m[4:7];
  logic [7:0] d[7:4];
  logic [2:0] i;

  initial begin
    mem[0] = 8'h00;
    mem[1] = 8'h11;
    mem[2] = 8'h22;
    mem[3] = 8'h33;
    addr = 2'd0;
  end

  initial
    for (int k = 4; k <= 7; k++) begin
      m[k] = 8'(k * 16);
      d[k] = 8'(k * 16 + 1);
    end

  assign i = 3'(4 + (cyc + 3) % 4);

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc  <= cyc + 1;
    addr <= addr + 2'd1;
    rd   <= mem[addr];
    $display("$[%0d| addr: %0d rd: %02x m1: %02x m3: %02x]", cyc, addr, rd, mem[1], mem[3]);
    $display("$[%0d| q: %0d]", cyc, q);
    $display("[%0d] m5=%02x m6=%02x d5=%02x d6=%02x m[%0d]=%02x d[%0d]=%02x", cyc, m[5], m[6],
             d[5], d[6], i, m[i], i, d[i]);
    if (cyc > 5) begin
      $display("*-* All Finished *-*");
      $finish;
    end
  end
endmodule

module sub (
  input  logic [7:0] a,
  output logic [7:0] q
);
  logic [7:0] mem [4];

  always_comb begin
    mem[0] = a;
    mem[1] = a + 8'd1;
    mem[2] = a + 8'd2;
    mem[3] = a + 8'd3;
  end

  assign q = mem[2];
endmodule
