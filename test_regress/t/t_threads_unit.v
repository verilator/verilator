// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`ifdef TEST_VLT
`define THREADS_UNIT
`else
`define THREADS_UNIT /*verilator threads_unit*/
`endif

// Both accesses must be combined before deciding whether a unit writes hazard_q.
module hazard_unit #(parameter int ID = 0);
  `THREADS_UNIT
  logic x;
  always_comb x = t.hazard_q[1-ID] ^ t.cyc[ID];
  always_comb t.hazard_q[ID] = x | t.cyc[ID];
endmodule

// A unit inside a unit; its logic belongs to its own instance, not the tile's
module acc (
    input clk,
    input [7:0] in,
    output [7:0] sum
);
  `THREADS_UNIT
  reg [7:0] s = 0;
  assign sum = s;
  always @(posedge clk) s <= s + in;
endmodule

module tile (
    input clk,
    input [7:0] id,
    input [7:0] in,
    output [7:0] out,
    output [7:0] st
);
  `THREADS_UNIT
  reg [7:0] r = 0;
  wire [7:0] sum;
  acc u (
      .clk(clk),
      .in(r),
      .sum(sum)
  );
  // The output depends on this tile's state, the next state on the previous tile's output
  assign out = r ^ id;
  assign st = r ^ sum;
  always @(posedge clk) r <= r + in + 8'd1;
endmodule

// A unit beside the tiles
module chk (
    input clk,
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);
  `THREADS_UNIT
  reg [7:0] s = 0;
  assign sum = s;
  always @(posedge clk) s <= s + (a ^ b);
endmodule

module t (
    input clk
);
  // Ignored, as the top module is the whole model
  `THREADS_UNIT
  integer cyc = 0;
  // The feedback reads become hybrid sensitivities, so dependency edges omit them.
  // verilator lint_off UNOPTFLAT
  logic [1:0] hazard_q = 0;
  // verilator lint_on UNOPTFLAT
  hazard_unit #(0) h0();
  hazard_unit #(1) h1();
  wire [7:0] out[4];
  wire [7:0] st[4];
  for (genvar i = 0; i < 4; ++i) begin : g
    tile u (
        .clk(clk),
        .id(8'(i * 17)),
        .in(out[(i+3)%4]),
        .out(out[i]),
        .st(st[i])
    );
  end
  wire [7:0] sum;
  chk c (
      .clk(clk),
      .a(st[0]),
      .b(st[2]),
      .sum(sum)
  );
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 20) begin
      `checkh(hazard_q, 2'b11)
      `checkd(st[0], 37)
      `checkd(st[1], 249)
      `checkd(st[2], 1)
      `checkd(st[3], 53)
      `checkd(sum, 184)
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule

`ifdef TEST_VLT
`verilator_config
threads_unit -module "acc"
threads_unit -module "chk"
threads_unit -module "hazard_unit"
threads_unit -module "tile"
// Ignored, as the top module is the whole model
threads_unit -module "t"
`ifdef TEST_HIERARCHICAL
hier_block -module "tile"
hier_workers -module "tile" -workers 2
// The ring of tiles is a combinational loop through the hierarchical block stubs
lint_off -rule UNOPTFLAT
`endif
`endif
