// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input logic clk,
    input logic [30:0] a,
    input logic [30:0] b,
    input logic [94:0] wide_a,
    input logic [94:0] wide_b,
    input logic [1:0] addr,
    input logic [14:0] seed,
    input logic reset,
    input logic enqueue,
    input logic dequeue,
    input logic [2:0][4:0] packed_in,
    output logic [30:0] quotient,
    output logic [30:0] remainder,
    output logic signed [30:0] signed_quotient,
    output logic signed [30:0] signed_remainder,
    output logic [94:0] wide_quotient,
    output logic [94:0] wide_remainder,
    output logic signed [94:0] wide_signed_quotient,
    output logic signed [94:0] wide_signed_remainder,
    output logic [14:0] rom_out,
    output logic [14:0] init_out,
    output logic [14:0] offset_out,
    output logic [14:0] ascending_out,
    output logic [14:0] initial_scalar,
    output logic [14:0] packed_out,
    output logic [14:0] registered_out,
    output logic [94:0] registered_wide,
    output logic [14:0] written0,
    output logic [14:0] written1,
    output logic [14:0] written2,
    output logic [4:0] table_out,
    output logic [30:0] chain_out,
    output logic [94:0] grouped0
`ifdef REPCUT_PUBLIC_CHAIN
    /* verilator public_flat_rw */
`endif
    ,
    output logic [94:0] grouped1, grouped2, grouped3,
    output logic [94:0] grouped4, grouped5, grouped6, grouped7
);
  typedef struct packed {
    logic [4:0] upper;
    logic [9:0] lower;
  } record_t;
  record_t record_value;
  logic [1:0] enq_ptr;
  logic [1:0] deq_ptr;
  logic maybe_full;
  always @(posedge clk) begin
    if (reset) begin
      enq_ptr <= 0;
      deq_ptr <= 0;
      maybe_full <= 0;
    end else begin
      if (enqueue) enq_ptr <= enq_ptr == 2 ? 2'b0 : enq_ptr + 2'b1;
      if (dequeue) deq_ptr <= deq_ptr == 2 ? 2'b0 : deq_ptr + 2'b1;
      if (enqueue != dequeue) maybe_full <= enqueue;
    end
  end
  assign table_out = {enq_ptr, deq_ptr, maybe_full};
  // Each intermediate has both a combinational and a clocked reader before
  // partition emission. The native chain becomes dead after those clocked
  // readers move into private partition code.
  for (genvar n = 0; n < 16; ++n) begin : chain
`ifdef REPCUT_PUBLIC_CHAIN
    wire [30:0] link_value /* verilator public_flat_rd */;
`else
    wire [30:0] link_value;
`endif
    logic [30:0] state_value;
    wire [30:0] accumulated;
    if (n == 0) begin
      assign link_value = (a ^ b) + 31'd1;
      assign accumulated = state_value;
    end else begin
      assign link_value = (chain[n-1].link_value << 1)
                         ^ (chain[n-1].link_value + a + 31'(n));
      assign accumulated = chain[n-1].accumulated ^ state_value;
    end
    always @(posedge clk) begin
      if (reset) state_value <= 0;
      else state_value <= link_value ^ (state_value + b);
    end
  end
  assign chain_out = chain[15].accumulated;
  logic [14:0] rom [0:2] = '{15'h1234, 15'h7654, 15'h1357};
  logic [14:0] initialized [0:2];
  logic [14:0] writable [0:2] = '{default: 15'b0};
  logic [2:0][4:0] offset_rom [3:1] = '{15'h1234, 15'h7654, 15'h1357};
  logic [14:0] ascending_rom [4:6] = '{15'h1234, 15'h7654, 15'h1357};
  initial begin
    if (seed[0]) initial_scalar = seed;
    else initial_scalar = seed ^ 15'h7b7b;
    initialized[0] = seed;
    initialized[1] = seed ^ 15'h5a5a;
    initialized[2] = seed + 15'd7;
  end
  assign quotient = a / b;
  assign remainder = a % b;
  assign signed_quotient = $signed(a) / $signed(b);
  assign signed_remainder = $signed(a) % $signed(b);
  assign wide_quotient = wide_a / wide_b;
  assign wide_remainder = wide_a % wide_b;
  assign wide_signed_quotient = $signed(wide_a) / $signed(wide_b);
  assign wide_signed_remainder = $signed(wide_a) % $signed(wide_b);
  assign rom_out = rom[addr];
  assign init_out = initialized[addr];
  assign offset_out = addr != 0 ? offset_rom[addr] : 15'b0;
  assign ascending_out = ascending_rom[{1'b1, addr}];
  assign record_value = {packed_in[0], packed_in[2], packed_in[1]};
  assign packed_out = record_value;
  always @(posedge clk) registered_out <= record_value ^ initialized[addr];
  always @(posedge clk) begin
    if (enqueue) writable[addr] <= packed_in;
    if (dequeue) writable[addr] <= packed_in ^ 15'h2a55;
  end
  assign written0 = writable[0];
  assign written1 = writable[1];
  assign written2 = writable[2];
  always @(posedge clk) begin
    if (reset) registered_wide <= 0;
    else if (enqueue)
      registered_wide <= dequeue ? wide_a / (wide_b | 95'd1) : wide_a ^ wide_b;
  end
  // Shared write paths, nested holds, repeated-write priority, and predicates
  // depending on state that publication itself changes. Cross-coupled RHSs
  // must all observe old state, including across partition boundaries.
  always @(posedge clk) begin
    if (reset) begin
      grouped0 <= 0;
      grouped1 <= 1;
      grouped2 <= 2;
      grouped3 <= 3;
      grouped4 <= 4;
      grouped5 <= 5;
      grouped6 <= 6;
      grouped7 <= 7;
    end else begin
      if (enqueue ^ grouped0[0]) begin
        grouped0 <= (grouped1 ^ wide_a) + 95'd1;
        grouped1 <= (grouped2 ^ wide_a) + 95'd2;
        grouped2 <= (grouped3 ^ wide_a) + 95'd3;
        grouped3 <= (grouped4 ^ wide_a) + 95'd4;
        grouped4 <= (grouped5 ^ wide_a) + 95'd5;
        grouped5 <= (grouped6 ^ wide_a) + 95'd6;
        grouped6 <= (grouped7 ^ wide_a) + 95'd7;
        grouped7 <= (grouped0 ^ wide_a) + 95'd8;
      end
      if (dequeue & grouped1[0]) begin
        grouped0 <= wide_b ^ 95'd11;
        grouped1 <= wide_b ^ 95'd12;
        grouped2 <= wide_b ^ 95'd13;
        grouped3 <= wide_b ^ 95'd14;
        grouped4 <= wide_b ^ 95'd15;
        grouped5 <= wide_b ^ 95'd16;
        grouped6 <= wide_b ^ 95'd17;
        grouped7 <= wide_b ^ 95'd18;
      end
    end
  end
endmodule
