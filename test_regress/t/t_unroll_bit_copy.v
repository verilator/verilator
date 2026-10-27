// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module bit_copy_case #(
    parameter W = 31,
    parameter D = 0,
    parameter S = 0
) (
    input clk,
    input logic [191:0] src
);
  logic [191:0] dst;
  logic [191:0] expected;
  always_comb begin
    dst = '1;
    for (int i = 0; i < W; i++) dst[D+i] = src[S+i];
  end
  always_comb begin
    expected = '1;
    expected[D+:W] = src[S+:W];
  end
  always @(posedge clk) `checkh(dst, expected);
endmodule

module t (
    input clk
);
  logic [1599:0] src = '1;
  int cycle = 0;
  always @(posedge clk) begin
    src <= {src[1567:0], $random};
    cycle <= cycle + 1;
    if (cycle == 128) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // Merged into one copy, except 'c65', which exceeds --unroll-count and stays a loop
  bit_copy_case #(31, 0, 0) c31 (
      clk,
      src[191:0]
  );
  bit_copy_case #(33, 7, 19) c33 (
      clk,
      src[191:0]
  );
  bit_copy_case #(64, 64, 32) c64 (
      clk,
      src[191:0]
  );
  bit_copy_case #(65, 3, 17) c65 (
      clk,
      src[191:0]
  );

  wire [63:0] src64 = src[63:0];

  // Descending indices, ascending packed ranges, the counter's exit value, and byte
  // lanes, which are copied separately
  // verilator lint_off ASCRANGE
  logic [3:34] ascending_src;
  logic [3:34] ascending_dst;
  // verilator lint_on ASCRANGE
  logic [127:0] reverse_dst;
  logic [95:0] counter_dst;
  int counter;
  logic [31:0] lanes;
  always_comb begin
    reverse_dst = '0;
    for (int i = 0; i < 32; i++) reverse_dst[90-i] = src[110-i];
    ascending_src = src64[31:0];
    for (int i = 0; i < 32; i++) ascending_dst[i+3] = ascending_src[i+3];
    counter_dst = '0;
    for (counter = 0; counter < 64; counter++) counter_dst[counter] = src[counter];
    counter_dst[95:64] = 32'(counter);
    for (int i = 0; i < 4; i++) lanes[8*i+:8] = src64[8*i+:8];
  end
  always @(posedge clk) begin
    `checkh(reverse_dst, {37'h0, src[110:79], 59'h0});
    `checkh(ascending_dst, src64[31:0]);
    `checkh(counter_dst, {32'd64, src64});
    `checkh(lanes, src64[31:0]);
  end

  // The Keccak state-layout conversions, in both directions
  typedef logic [4:0][4:0][63:0] box_t;
  function automatic box_t bitarray_to_box(logic [1599:0] bits_in);
    box_t box;
    for (int y = 0; y < 5; y++)
    for (int x = 0; x < 5; x++) for (int z = 0; z < 64; z++) box[x][y][z] = bits_in[64*(5*y+x)+z];
    return box;
  endfunction
  function automatic logic [1599:0] box_to_bitarray(box_t box);
    logic [1599:0] bits_out;
    for (int y = 0; y < 5; y++)
    for (int x = 0; x < 5; x++) for (int z = 0; z < 64; z++) bits_out[64*(5*y+x)+z] = box[x][y][z];
    return bits_out;
  endfunction
  box_t transpose_expected;
  logic [1599:0] inverse_expected;
  for (genvar x = 0; x < 5; x++) begin
    for (genvar y = 0; y < 5; y++) begin
      assign transpose_expected[x][y] = src[64*(5*y+x)+:64];
      assign inverse_expected[64*(5*y+x)+:64] = src[64*(5*x+y)+:64];
    end
  end
  wire [1599:0] transpose = bitarray_to_box(src);
  wire [1599:0] inverse = box_to_bitarray(src);
  always @(posedge clk) begin
    `checkh(transpose, transpose_expected);
    `checkh(inverse, inverse_expected);
  end

  // Copies that must not merge: within one variable, in opposite directions, with a
  // stride, under a condition, with the destination overwritten between copies, and
  // past the end of the destination
  logic [63:0] overlap;
  logic [63:0] reversed;
  logic [63:0] step2;
  logic [63:0] gated;
  logic [7:0] clobber;
  logic [5:0] past_end;
  wire enable = src[80];
  wire [63:0] reverse_bits = {<<{src64}};
  always_comb begin
    overlap = src64;
    for (int i = 0; i < 63; i++) overlap[i+1] = overlap[i];
    reversed = '0;
    for (int i = 0; i < 64; i++) reversed[i] = src64[63-i];
    step2 = '0;
    for (int i = 0; i < 64; i += 2) step2[i] = src64[i];
    gated = '1;
    for (int i = 0; i < 64; i++) if (enable) gated[i] = src64[i];
    for (int i = 0; i < 8; i++) begin
      clobber = '0;
      clobber[i] = src64[i];
    end
    past_end = '0;
    // verilator lint_off SELRANGE
    for (int i = 0; i < 8; i++) past_end[i] = src64[i];
    // verilator lint_on SELRANGE
  end
  always @(posedge clk) begin
    `checkh(overlap, {64{src64[0]}});
    `checkh(reversed, reverse_bits);
    `checkh(step2, src64 & 64'h5555_5555_5555_5555);
    `checkh(gated, enable ? src64 : '1);
    `checkh(clobber, {src64[7], 7'h0});
    `checkh(past_end, src64[5:0]);
  end

  // A copy inside an unrolled loop, with another statement in the body, replacing a
  // constant destination; a packed structure member; and a function called twice
  typedef struct packed {
    logic [3:0] a;
    logic [11:0] f;
    logic [7:0] g;
  } member_t;
  member_t member_src;
  member_t member_dst;
  logic [7:0] bound_dst;
  logic [7:0] bound_out[4];
  int updates;
  function automatic logic [15:0] shift_copy(logic [15:0] v);
    logic [15:0] r;
    r = '0;
    for (int k = 0; k < 8; k++) r[k+4] = v[k];
    return r;
  endfunction
  assign member_src = src[23:0];
  always_comb begin
    updates = 0;
    for (int j = 0; j < 4; j++) begin
      bound_dst = 8'h5a;
      for (int i = 0; i < 6; i++) begin
        bound_dst[i] = src[8*j+i];
        updates++;
      end
      bound_out[j] = bound_dst;
    end
    member_dst = '0;
    for (int i = 0; i < 8; i++) member_dst.f[i+2] = member_src.g[i];
  end
  always @(posedge clk) begin
    for (int j = 0; j < 4; j++) `checkh(bound_out[j], {2'b01, src[8*j+:6]});
    `checkh(updates, 24);
    `checkh(member_dst, {6'h0, src[7:0], 10'h0});
    `checkh(shift_copy(src[15:0]), {4'h0, src[7:0], 4'h0});
    `checkh(shift_copy(src[47:32]), {4'h0, src[39:32], 4'h0});
  end

  // Nonblocking copies are not merged
  logic [63:0] nba_dst;
  logic [63:0] nba_expected;
  always @(posedge clk) begin
    for (int i = 0; i < 64; i++) nba_dst[i] <= src64[i];
    nba_expected <= src64;
    if (cycle != 0) `checkh(nba_dst, nba_expected);
  end
endmodule
