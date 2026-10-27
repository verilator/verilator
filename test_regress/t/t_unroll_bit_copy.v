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

  bit_copy_case #(31, 0, 0) c31 (
      clk,
      src[191:0]
  );
  bit_copy_case #(33, 7, 19) c33 (
      clk,
      src[191:0]
  );
  bit_copy_case #(63, 32, 64) c63 (
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
  bit_copy_case #(95, 65, 31) c95 (
      clk,
      src[191:0]
  );

  bit_copy_case #(33, 0, 17) no_d (
      clk,
      src[191:0]
  );
  bit_copy_case #(63, 19, 0) no_s (
      clk,
      src[191:0]
  );

  // Both descending indices preserve order in the resulting packed slice.
  logic [127:0] reverse_dst;
  logic [127:0] reverse_expected;
  always_comb begin
    reverse_dst = '0;
    for (int i = 0; i < 32; i++) reverse_dst[90-i] = src[110-i];
    reverse_expected = '0;
    reverse_expected[59+:32] = src[79+:32];
  end
  always @(posedge clk) `checkh(reverse_dst, reverse_expected);

  // Ascending and nonzero packed bounds, including typedefs.
  // verilator lint_off ASCRANGE
  typedef logic [3:34] ascending_t;
  // verilator lint_on ASCRANGE
  ascending_t ascending_src;
  ascending_t ascending_dst;
  assign ascending_src = src[31:0];
  always_comb begin
    for (int i = 0; i < 32; i++) ascending_dst[i+3] = ascending_src[i+3];
  end
  always @(posedge clk) `checkh(ascending_dst, src[31:0]);

  logic [95:0] counter_dst;
  int counter;
  always_comb begin
    counter_dst = '0;
    for (counter = 0; counter < 64; counter++) counter_dst[counter] = src[counter];
    counter_dst[95:64] = 32'(counter);
  end
  always @(posedge clk) begin
    `checkh(counter, 64);
    `checkh(counter_dst, {32'd64, src[63:0]});
  end

  // The original Keccak state-layout conversion, in both directions. Structural
  // lane wiring supplies the independent oracle, without another bit-copy loop.
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

  // Negative cases must retain the sequential loop semantics.
  logic [63:0] overlap;
  logic [63:0] truncated;
  logic [63:0] wrapped;
  logic [63:0] gated;
  logic [63:0] disabled;
  logic [63:0] reversed;
  logic [30:0] partial;
  logic [63:0] extra;
  int updates;
  wire [63:0] src64 = src[63:0];
  wire enable = src[80];
  always_comb begin
    overlap = src64;
    for (int i = 0; i < 63; i++) overlap[i+1] = overlap[i];
    truncated = '0;
    for (int i = 0; i < 64; i++) truncated[i] = src64[6'(i[3:0])];
    wrapped = '0;
    for (int i = 0; i < 64; i++) wrapped[i] = src64[6'(i+8)];
    gated = '1;
    for (int i = 0; i < 64; i++) if (enable) gated[i] = src64[i];
    disabled = '0;
    /* verilator unroll_disable */
    for (int i = 0; i < 64; i++) begin
      disabled[i] = src64[i];
    end
    reversed = '0;
    for (int i = 0; i < 64; i++) reversed[i] = src64[63-i];
    partial = '1;
    for (int i = 0; i < 27; i++) partial[i+5] = src64[i];
    extra = '0;
    updates = 0;
    for (int i = 0; i < 64; i++) begin
      extra[i] = src64[i];
      updates++;
    end
  end
  wire [63:0] reverse_bits = {<<{src64}};
  always @(posedge clk) begin
    `checkh(overlap, {64{src64[0]}});
    `checkh(truncated, {4{src64[15:0]}});
    `checkh(wrapped, {src64[7:0], src64[63:8]});
    `checkh(gated, enable ? src64 : '1);
    `checkh(disabled, src64);
    `checkh(reversed, reverse_bits);
    `checkh(partial, {src64[25:0], 5'b11111});
    `checkh(extra, src64);
    `checkh(updates, 64);
  end

  // A constant destination binding is invalidated by the first bit write. It
  // cannot be substituted into either index, even when source and destination differ.
  logic [63:0] self_index;
  logic [63:0] self_expected;
  always_comb begin
    self_index = '0;
    for (int i = 0; i < 64; i++) self_index[6'(i+32'(self_index[2:0]))] = src64[i];
    self_expected = '0;
    /* verilator unroll_disable */
    for (int i = 0; i < 64; i++) self_expected[6'(i+32'(self_expected[2:0]))] = src64[i];
  end
  always @(posedge clk) `checkh(self_index, self_expected);

  // A copy inside an unrolled loop invalidates the constant binding of its destination
  logic [7:0] bound_dst;
  logic [7:0] bound_out[4];
  always_comb begin
    for (int j = 0; j < 4; j++) begin
      bound_dst = 8'h5a;
      for (int i = 0; i < 6; i++) bound_dst[i] = src[8*j+i];
      bound_out[j] = bound_dst;
    end
  end
  always @(posedge clk) begin
    for (int j = 0; j < 4; j++) `checkh(bound_out[j], {2'b01, src[8*j+:6]});
  end

  // Packed structure members, and a narrow signed counter whose exit value is read
  typedef struct packed {
    logic [3:0] a;
    logic [11:0] f;
    logic [7:0] g;
  } member_t;
  member_t member_src;
  member_t member_dst;
  logic [15:0] narrow_dst;
  logic signed [3:0] narrow_i;
  wire [15:0] src16 = src[15:0];
  assign member_src = src[23:0];
  always_comb begin
    member_dst = '0;
    for (int i = 0; i < 8; i++) member_dst.f[i+2] = member_src.g[i];
    narrow_dst = '0;
    for (narrow_i = 0; narrow_i < 7; narrow_i++) narrow_dst[narrow_i+2] = src16[narrow_i];
  end
  always @(posedge clk) begin
    `checkh(member_dst, {6'h0, src[7:0], 10'h0});
    `checkh(narrow_dst, {7'h0, src[6:0], 2'b00});
    `checkh(narrow_i, 4'sd7);
  end

  // A copy in a function called twice, and a declined copy to a public destination
  function automatic logic [15:0] shift_copy(logic [15:0] v);
    logic [15:0] r;
    r = '0;
    for (int k = 0; k < 8; k++) r[k+4] = v[k];
    return r;
  endfunction
  // verilator lint_off UNOPTPUBLIC
  logic [63:0] public_dst  /* verilator public_flat_rw */;
  // verilator lint_on UNOPTPUBLIC
  always_comb begin
    public_dst = '0;
    for (int i = 0; i < 64; i++) public_dst[i] = src64[i];
  end
  always @(posedge clk) begin
    `checkh(shift_copy(src[15:0]), {4'h0, src[7:0], 4'h0});
    `checkh(shift_copy(src[47:32]), {4'h0, src[39:32], 4'h0});
    `checkh(public_dst, src64);
  end

  // A signed outer index is accepted while its sign bit is clear. The remaining loops
  // must keep their sequential semantics: a wide or unbound offset, a negative signed
  // offset, a variable shift, unsupported operators, a signed guard it cannot prove, and
  // increments other than 'i = i + 1'.
  // verilator lint_off WIDTH
  logic [63:0] signed_dst;
  logic [63:0] wide_dst;
  logic [63:0] unbound_dst;
  logic [63:0] negative_dst;
  logic [63:0] shifted_dst;
  logic [63:0] xor_dst;
  logic [63:0] not_dst;
  logic [31:0] guarded_dst;
  logic [63:0] step2_dst;
  logic [63:0] cast_dst;
  logic [69:0] wide_off;
  logic signed [3:0] negative_off;
  wire [2:0] unbound_off = src[90:88];
  int cast_i;
  always_comb begin
    signed_dst = '0;
    for (byte j = 0; j < 4; j++) begin
      for (int i = 0; i < 8; i++) signed_dst[8*j+i] = src64[8*j+i];
    end
    wide_off = 70'd5;
    wide_dst = '0;
    for (int i = 0; i < 32; i++) wide_dst[i+wide_off] = src64[i];
    unbound_dst = '0;
    for (int i = 0; i < 32; i++) unbound_dst[i+32'(unbound_off)] = src64[i];
    negative_off = -4'sd8;
    negative_dst = '0;
    for (int i = 0; i < 32; i++) negative_dst[i+8+negative_off] = src64[i];
    shifted_dst = '0;
    for (int i = 0; i < 5; i++) shifted_dst[i] = src64[2<<i];
    xor_dst = '0;
    for (int i = 0; i < 32; i++) xor_dst[i] = src64[i^1];
    not_dst = '0;
    for (int i = 0; i < 32; i++) not_dst[i] = src64[6'(~i)];
    guarded_dst = '1;
    for (int i = 0; i < 24; i++) if (5'sd15 >= $signed(5'(i))) guarded_dst[i] = src64[i];
    step2_dst = '0;
    for (int i = 0; i < 64; i += 2) step2_dst[i] = src64[i];
    cast_dst = '0;
    for (cast_i = 0; cast_i < 32; cast_i = 32'(cast_i[7:0]) + 1) cast_dst[cast_i] = src64[cast_i];
  end
  // verilator lint_on WIDTH
  wire [63:0] even_bits = src64 & 64'h5555_5555_5555_5555;
  wire [31:0] swapped_pairs = {
    src64[30], src64[31], src64[28], src64[29], src64[26], src64[27], src64[24], src64[25],
    src64[22], src64[23], src64[20], src64[21], src64[18], src64[19], src64[16], src64[17],
    src64[14], src64[15], src64[12], src64[13], src64[10], src64[11], src64[8], src64[9],
    src64[6], src64[7], src64[4], src64[5], src64[2], src64[3], src64[0], src64[1]
  };
  always @(posedge clk) begin
    `checkh(signed_dst, {32'h0, src64[31:0]});
    `checkh(wide_dst, {27'h0, src64[31:0], 5'h0});
    `checkh(unbound_dst, 64'(src64[31:0]) << unbound_off);
    `checkh(negative_dst, {32'h0, src64[31:0]});
    `checkh(shifted_dst, {59'h0, src64[32], src64[16], src64[8], src64[4], src64[2]});
    `checkh(xor_dst, {32'h0, swapped_pairs});
    `checkh(guarded_dst, {8'hff, src64[23:0]});
    `checkh(not_dst, {32'h0, reverse_bits[31:0]});
    `checkh(step2_dst, even_bits);
    `checkh(cast_dst, {32'h0, src64[31:0]});
  end

  logic [63:0] nba_dst;
  logic [63:0] nba_expected;
  always @(posedge clk) begin
    for (int i = 0; i < 64; i++) nba_dst[i] <= src64[i];
    nba_expected <= src64;
    if (cycle != 0) `checkh(nba_dst, nba_expected);
  end
endmodule
