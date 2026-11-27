// DESCRIPTION: Verilator: RepCut partial memory writes and ordered publication
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026-2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t #(
  parameter PUBLICATION_WORDS = 0,
  localparam PUBLICATION_BITS = PUBLICATION_WORDS != 0 ? 32*PUBLICATION_WORDS : 1
) (
  input bit clk, clk_b,
  input logic [5:0] enables,
  input logic [2:0] address, other,
  input logic [6:0] offset,
  input logic [94:0] data,
  output logic [94:0] wide_out, wide_old, cross_old, retained_old,
  output logic [14:0] small_out, small_old,
  output logic [62:0] long_out, long_old,
  output wire [2*PUBLICATION_BITS-1:0] publication, publication_old
);
  // Large banks make the automatic policy select parallel publication. The
  // second clock observes old state, so these writes cannot publish early.
  for (genvar g = 0; g < 2; ++g) begin : publication_banks
    if (PUBLICATION_WORDS != 0) begin : enabled
      logic [PUBLICATION_BITS-1:0] value, previous;
      always @(posedge clk)
        value <= (value << 1) ^ {PUBLICATION_WORDS{data[31:0]}} ^ PUBLICATION_BITS'(g+1);
      always @(posedge clk_b) previous <= value;
      assign publication[g*PUBLICATION_BITS+:PUBLICATION_BITS] = value;
      assign publication_old[g*PUBLICATION_BITS+:PUBLICATION_BITS] = previous;
    end else begin : disabled
      assign publication[g*PUBLICATION_BITS+:PUBLICATION_BITS] = '0;
      assign publication_old[g*PUBLICATION_BITS+:PUBLICATION_BITS] = '0;
    end
  end
  typedef logic [94:0] wide_t;
  typedef logic [0:62] ascending_t;
  wide_t wide_mem [1:3];
  logic [14:0] small_mem [3:1];
  ascending_t long_mem [0:4];
  assign wide_out = (address >= 1 && address <= 3) ? wide_mem[address] : '0;
  assign small_out = (address >= 1 && address <= 3) ? small_mem[address] : '0;
  assign long_out = address <= 4 ? long_mem[address] : '0;
  always @(posedge clk) begin
    wide_old <= wide_out;
    small_old <= small_out;
    long_old <= long_out;
    if (enables[0] && address >= 1 && address <= 3) wide_mem[address] <= data;
    if (enables[1] && address >= 1 && address <= 3) wide_mem[address][7 +: 33] <= data[32:0];
    // Keep this slice contained or wholly outside the element. Stock v5.050
    // corrupts an adjacent element for a dynamic slice crossing the final word.
    if (enables[2] && address >= 1 && address <= 3 && (offset <= 78 || offset >= 95)) wide_mem[address][offset +: 17] <= data[16:0];
    if (enables[3] && other >= 1 && other <= 3) wide_mem[other][31 +: 33] <= wide_out[32:0] ^ data[32:0];
    if (enables[4] && address >= 1 && address <= 3) wide_mem[address][94] <= data[3];
    if (enables[5] && address >= 1 && address <= 3) wide_mem[address] <= ~data;
  end
  always @(posedge clk) begin
    if (enables[0] && address >= 1 && address <= 3) small_mem[address] <= data[14:0];
    if (enables[1] && address >= 1 && address <= 3) small_mem[address][offset[3:0] +: 7] <= data[6:0];
    if (enables[2] && other >= 1 && other <= 3) small_mem[other][3 +: 7] <= small_out[6:0] ^ data[13:7];
  end
  always @(posedge clk) begin
    if (enables[0]) long_mem[address] <= data[62:0];
    if (enables[1]) long_mem[address][25 +: 17] <= data[16:0];
    if (enables[2]) long_mem[other][62] <= long_out[0] ^ data[4];
  end
`ifdef REPCUT_SINGLE_CLOCK
  always @(posedge clk) cross_old <= wide_out;
  assign retained_old = cross_old;
`else
  always @(posedge clk_b) cross_old <= wide_out;
  // Real conversion keeps this old-state reader in the ordinary scheduler.
  always @(posedge clk_b) retained_old <= wide_out ^ 95'(int'(real'(address)));
`endif
endmodule
