// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2026 by Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

// Test: nested parameterized interface with struct typedef used as type parameter
//
// Reproduces a bug where specializeNestedIfaceCells causes early
// specialization of a nested interface, leaving PARAMTYPEDTYPE child
// REFDTYPEs pointing to the template struct instead of the clone struct.
// The struct's width then resolves using the template's default parameter
// values instead of the actual overridden values.
//
// Pattern (mirrors Aerial's simple_cache / simple_cache_if / simple_cache_types_if):
//   1. A wrapper interface instantiates a nested types interface
//   2. The types interface computes localparams from cfg (using $clog2/division)
//   3. Those localparams define typedef ranges for struct members
//   4. A module receives the wrapper interface as a port, also instantiates
//      the types interface locally, and uses the struct typedef
//   5. Both the wrapper and the module use the same cfg, so they share
//      the same types_if clone via "De-parameterize to prev"

package cfg_pkg;
  typedef struct packed {
    logic [31:0] AddrBits;
    logic [31:0] Capacity;
    logic [31:0] LineSize;
    logic [31:0] Associativity;
  } cfg_t;
endpackage

// Nested types interface: derives struct typedef from computed localparams
interface types_if #(
  parameter cfg_pkg::cfg_t cfg = '0
)();
  // Computed localparams — these use division and $clog2 of cfg fields.
  // With default cfg='0, these produce X/undefined values.
  localparam int NUM_LINES     = cfg.Capacity / cfg.LineSize;
  localparam int LINES_PER_WAY = NUM_LINES / cfg.Associativity;
  localparam int BLOCK_BITS    = $clog2(cfg.LineSize);
  localparam int ROW_BITS      = $clog2(LINES_PER_WAY);
  localparam int TAG_BITS      = cfg.AddrBits - ROW_BITS - BLOCK_BITS;

  typedef logic [TAG_BITS-1:0] tag_t;
  typedef logic [ROW_BITS-1:0] row_t;
  typedef logic [BLOCK_BITS-1:0] block_t;

  typedef struct packed {
    logic  vld;
    tag_t  tag;
    row_t  row;
    block_t block;
  } entry_t;
endinterface

// Wrapper interface: instantiates types_if as a nested cell
// (mirrors simple_cache_if which instantiates simple_cache_types_if)
interface wrapper_if #(
  parameter cfg_pkg::cfg_t cfg = '0
)();
  types_if #(cfg) types();

  typedef types.tag_t   tag_t;

  logic  req_vld;
  tag_t  req_tag;
endinterface

// Sub-module parameterized by entry width
// (mirrors flop_nr / sram_generic_1r1w parameterized by $bits(sc_tag_t))
module entry_store #(
  parameter int ENTRY_WIDTH = 8,
  parameter int DEPTH = 4
)(
  input  logic clk,
  input  logic wr_en,
  input  logic [ENTRY_WIDTH-1:0] wr_data,
  output logic [ENTRY_WIDTH-1:0] rd_data
);
  logic [ENTRY_WIDTH-1:0] mem [DEPTH];
  always_ff @(posedge clk) begin
    if (wr_en) mem[0] <= wr_data;
  end
  assign rd_data = mem[0];
endmodule

// Inner module: receives wrapper_if as port, instantiates types_if locally,
// uses struct typedef from types_if
// (mirrors simple_cache which receives simple_cache_if, instantiates
//  simple_cache_types_if, and uses types.sc_tag_t)
module inner_mod #(
  parameter cfg_pkg::cfg_t cfg = '0
)(
  input logic clk,
  wrapper_if io
);
  // Local instantiation of types_if — same cfg, so gets same clone
  // as the one inside wrapper_if via "De-parameterize to prev"
  types_if #(cfg) types();

  typedef types.entry_t entry_t;
  typedef types.tag_t tag_t;

  entry_t wr_entry;
  entry_t rd_entry;

  assign wr_entry.vld   = io.req_vld;
  assign wr_entry.tag   = io.req_tag;
  assign wr_entry.row   = '0;
  assign wr_entry.block = '0;

  // Use $bits of the struct typedef as a value parameter to sub-module.
  // This is the critical pattern: $bits(entry_t) must resolve using the
  // clone's struct (correct width), not the template's (zero/X width).
  entry_store #(
    .ENTRY_WIDTH($bits(entry_t)),
    .DEPTH(8)
  ) u_store (
    .clk(clk),
    .wr_en(io.req_vld),
    .wr_data(wr_entry),
    .rd_data(rd_entry)
  );
endmodule

// Outer wrapper module: instantiates wrapper_if and inner_mod
// (mirrors mblit_simple_cache_wrap)
module outer_mod #(
  parameter cfg_pkg::cfg_t cfg = '0
)(
  input logic clk
);
  wrapper_if #(cfg) wif();

  inner_mod #(cfg) u_inner (
    .clk(clk),
    .io(wif)
  );
endmodule

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  int cyc = 0;

  // Non-default config:
  //   AddrBits=64, Capacity=1024, LineSize=64, Associativity=2
  //   NUM_LINES = 1024/64 = 16
  //   LINES_PER_WAY = 16/2 = 8
  //   BLOCK_BITS = $clog2(64) = 6
  //   ROW_BITS = $clog2(8) = 3
  //   TAG_BITS = 64 - 3 - 6 = 55
  //   entry_t = 1 + 55 + 3 + 6 = 65 bits
  localparam cfg_pkg::cfg_t MY_CFG = '{
    AddrBits: 64,
    Capacity: 1024,
    LineSize: 64,
    Associativity: 2
  };

  outer_mod #(.cfg(MY_CFG)) u_outer (.clk(clk));

  always @(posedge clk) begin
    cyc <= cyc + 1;

    u_outer.wif.req_vld <= (cyc[0] == 1'b1);
    u_outer.wif.req_tag <= 55'(cyc);

    if (cyc > 5) begin
      // Verify the struct round-trips correctly
      if (u_outer.u_inner.rd_entry.vld !== 1'b1 && cyc > 10) begin
        $display("FAIL cyc=%0d: rd_entry.vld=%b expected 1",
                 cyc, u_outer.u_inner.rd_entry.vld);
        $stop;
      end
    end

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
