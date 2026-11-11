// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A C-style '[size]' packed dimension is non-standard (IEEE 1800-2023 7.4.1), but accepted as
// other simulators do, meaning '[0:size-1]' as for an unpacked dimension (IEEE 1800-2023 7.4.2)

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

localparam int WORDS = 2;
localparam int WORD_WIDTH = 64;

class Monitor;
  // Function arguments of 2 dimensions, in a class, as in the issue
  function longint get_val(logic [127:0] indata, logic [WORDS][WORD_WIDTH/8] be);
    int offset = 0;
    longint res = '0;
    `checkd($right(be, 1), WORDS - 1);
    `checkd($right(be, 2), WORD_WIDTH / 8 - 1);
    for (int i = 0; i < WORDS; ++i) begin
      for (int j = 0; j < WORD_WIDTH / 8; ++j) begin
        if (be[i][j]) begin
          res[offset*8+:8] = indata[7:0];
          indata >>= 8;
          ++offset;
        end
      end
    end
    return res;
  endfunction
endclass

module t (
    input clk
);

  int cyc = 0;
  logic [63:0] crc = 64'h5aef0c8d_d70a4497;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  // A variable is ascending, so its index 0 is the most significant bit
  always @(posedge clk) begin
    automatic logic [7] v = crc[6:0];
    automatic int i = int'(crc[10:8]) % 7;
    `checkd($left(v), 0);
    `checkd($right(v), 6);
    `checkh(v[0], crc[6]);
    `checkh(v[6], crc[0]);
    `checkh(v[i], crc[6-i]);
    `checkh(v[1:3], crc[5:3]);
  end

  // A wide variable
  always @(posedge clk) begin
    automatic logic [65] v = {1'b1, crc};
    `checkd($bits(v), 65);
    `checkh(v[0], 1'b1);
    `checkh(v[1:64], crc);
  end

  // 2 dimensions
  always @(posedge clk) begin
    automatic logic [3][5] v = crc[14:0];
    `checkd($left(v, 1), 0);
    `checkd($right(v, 1), 2);
    `checkd($left(v, 2), 0);
    `checkd($right(v, 2), 4);
    `checkh(v[0], crc[14:10]);
    `checkh(v[2][4], crc[0]);
    `checkh(v[1:2], crc[9:0]);
  end

  // 3 dimensions
  always @(posedge clk) begin
    automatic logic [3][5][7] v = {crc[40:0], crc};
    `checkd($bits(v), 105);
    `checkd($right(v, 1), 2);
    `checkd($right(v, 2), 4);
    `checkd($right(v, 3), 6);
    `checkh(v[0], crc[40:6]);
    `checkh(v[1][2], crc[55:49]);
    `checkh(v[2][4][6], crc[0]);
  end

  // Mixed with ranges
  always @(posedge clk) begin
    automatic logic [3:1][2] v = crc[5:0];
    automatic logic [2][3:1] w = crc[5:0];
    `checkh(v[3], crc[5:4]);
    `checkh(v[1][1], crc[0]);
    `checkh(w[0], crc[5:3]);
    `checkh(w[1][1], crc[0]);
  end

  // Typedefs, of a type and of a type identifier, and variables of a type identifier
  typedef logic [5] five_t;
  typedef five_t [3] five3_t;
  typedef five_t [WORDS] five_words_t;
  five_t [WORDS] five_words;
  assign five_words = crc[9:0];
  always @(posedge clk) begin
    automatic five3_t v = crc[14:0];
    automatic five_t [2] w = crc[9:0];
    `checkd($right(five_t), 4);
    `checkd($right(five3_t, 1), 2);
    `checkd($right(five_words_t, 1), WORDS - 1);
    `checkh(v[0], crc[14:10]);
    `checkh(v[2][4], crc[0]);
    `checkh(w[1][0], crc[4]);
    `checkh(five_words[1][0], crc[4]);
  end

  // Packed struct members, and an array of packed structs
  typedef struct packed {
    logic [3] a;
    logic [4] b;
  } ab_t;
  always @(posedge clk) begin
    automatic ab_t [2] v = crc[13:0];
    `checkh(v[0].a[0], crc[13]);
    `checkh(v[1].a, crc[6:4]);
    `checkh(v[1].b[3], crc[0]);
  end

  // Function arguments and return types
  function automatic logic [5] keep_index0(input [5] a);
    `checkd($right(a), 4);
    keep_index0 = '0;
    keep_index0[0] = a[0];
  endfunction
  always @(posedge clk) begin
    `checkh(keep_index0(crc[4:0]), {crc[4], 4'b0});
  end

  // Function arguments of 2 dimensions, in a class, as in the issue
  Monitor mon = new;
  always @(posedge clk) begin
    `checkh(mon.get_val(128'h0123_4567_89ab_cdef_1122_3344_5566_7788, 16'h000f), 64'h5566_7788);
  end

  // Nets and ports
  wire [5] net5 = crc[4:0];
  wire [5] rotated;
  sub_rotate u_sub (
      .in(net5),
      .out(rotated)
  );
  always @(posedge clk) begin
    `checkh(net5[0], crc[4]);
    `checkh(rotated, {crc[3:0], crc[4]});
  end

  // Parameters
  localparam [4] P = 4'b0001;
  always @(posedge clk) begin
    `checkh(P[3], 1'b1);
  end

  // Unlike a packed dimension, a C-style gate instance array warns of its ascending range
  wire [WORDS-1:0] gate_out;
  buf gates[WORDS] (gate_out, crc[WORDS-1:0]);
  always @(posedge clk) begin
    `checkh(gate_out, crc[WORDS-1:0]);
  end

endmodule

module sub_rotate (
    input logic [5] in,
    output [5] out
);
  assign out = {in[1:4], in[0]};
endmodule
