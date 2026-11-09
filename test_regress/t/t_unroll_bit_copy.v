// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 1'b0;
  always #5 clk = ~clk;

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

  // The Keccak state-layout conversions. Unrolled, they only fit within --unroll-stmts
  // when the destination index is folded.
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
endmodule
