// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Lane Brooks
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef logic [67:3] unpacked_word_t;
typedef unpacked_word_t unpacked_words_t [3:1];
typedef logic [6:0] unpacked_matrix_t [2:4][5:4];

module top (
    input A,
    input B,
    input SEL,
    input clk,
    output Y1,
    output Y2,
    output Z,
    output done
);
  io io1 (
      .A(A),
      .OE(SEL),
      .Z(Z),
      .Y(Y1)
  );
  pass io2 (
      .A(B),
      .OE(!SEL),
      .Z(Z),
      .Y(Y2)
  );
  assign Z = 1'bz;

  pad_checker u_pad_checker (
      .clk(clk),
      .done(done)
  );
endmodule

module pass (
    input A,
    input OE,
    inout Z,
    output Y
);
  io_noinline io (
      .A(A),
      .OE(OE),
      .Z(Z),
      .Y(Y)
  );
  assign Z = 1'bz;
endmodule

module io (
    input A,
    input OE,
    inout Z,
    output Y
);
  assign Z = (OE) ? A : 1'bz;
  assign Y = Z;
  assign Z = 1'bz;
endmodule

module io_noinline (
    input A,
    input OE,
    inout Z,
    output Y
);
  /*verilator no_inline_module*/
  assign Z = (OE) ? A : 1'bz;
  assign Y = Z;
  assign Z = 1'bz;
endmodule


module pad_checker (
    input wire clk,
    output wire done
);
  wire tri_pad;
  reg [1:0] ie = '0;
  reg [1:0] oe = '0;
  reg [1:0] in = '0;
  wire out_0, out_1;

  tri_pad u_pad0 (
      .pad(tri_pad),
      .ie(ie[0]),
      .oe(oe[0]),
      .to_pad(in[0]),
      .from_pad(out_0)
  );
  tri_pad u_pad1 (
      .pad(tri_pad),
      .ie(ie[1]),
      .oe(oe[1]),
      .to_pad(in[1]),
      .from_pad(out_1)
  );

  wire bin_pad_in_0, bin_pad_in_1;
  wire bin_pad_01, bin_pad_10;
  wire bin_pad_en_01, bin_pad_en_10;
  wire bin_from_pad_out_0, bin_from_pad_out_1;
  wire bin_from_pad_en_0, bin_from_pad_en_1;

  // Expectation model that simulates how Verilator solves tri-state
  pad_binary u_pad_bin_0 (
      .pad_in(bin_pad_in_0),
      .pad_out(bin_pad_01),
      .pad_en(bin_pad_en_01),
      .ie(ie[0]),
      .oe(oe[0]),
      .to_pad(in[0]),
      .from_pad_out(bin_from_pad_out_0),
      .from_pad_en(bin_from_pad_en_0)
  );

  pad_binary u_pad_bin_1 (
      .pad_in(bin_pad_in_1),
      .pad_out(bin_pad_10),
      .pad_en(bin_pad_en_10),
      .ie(ie[1]),
      .oe(oe[1]),
      .to_pad(in[1]),
      .from_pad_out(bin_from_pad_out_1),
      .from_pad_en(bin_from_pad_en_1)
  );

  assign bin_pad_in_0 = (bin_pad_en_10 & bin_pad_10) | (bin_pad_en_01 & bin_pad_01);
  assign bin_pad_in_1 = (bin_pad_en_01 & bin_pad_01) | (bin_pad_en_10 & bin_pad_10);


  logic done_reg = 0;
  assign done = done_reg;
  always @(posedge clk) begin
    if ({ie, oe, in} == 6'b111111) begin
      done_reg <= 1'b1;
    end
    else begin
      if (out_0 != bin_from_pad_out_0) begin
        $display("ie:%b oe:%b in:%b out0 act:%b exp:%b", ie[0], oe[0], in[0], out_0,
                 bin_from_pad_out_0);
        $stop;
      end
      if (out_1 != bin_from_pad_out_1) begin
        $display("ie:%b oe:%b in:%b out1 act:%b exp:%b", ie[1], oe[1], in[1], out_1,
                 bin_from_pad_out_1);
        $stop;
      end
      // Let's try all combination
      {ie, oe, in} <= {ie, oe, in} + 1;
    end
  end

  // Exercise wide and packed multidimensional inouts across a hierarchy boundary.
  wire [5:0] cyc = {ie, oe, in};
  wire [67:3] en = 65'h15555555555555555 ^ {65{cyc[0]}} ^ (65'(cyc) << 31);
  wire [67:3] data = 65'h123456789abcdef01 ^ 65'(cyc) ^ (65'(cyc) << 59);
  wire [67:3] external_data = ~data;
  wire [67:3] expected = (en & data) | (~en & external_data);
  wire [67:3] pad;
  wire [1:0][4:2] matrix_pad;
  wire [1:0][4:2] matrix_data = {data[8:6], data[5:3]};
  wire [1:0][4:2] matrix_en = {en[8:6], en[5:3]};
  wire [1:0][4:2] matrix_external = ~matrix_data;
  wire [1:0][4:2] matrix_expected = (matrix_en & matrix_data) | (~matrix_en & matrix_external);
  /* verilator lint_off ASCRANGE */
  wire [2:8] reverse_pad;
  /* verilator lint_on ASCRANGE */
  wire [6:0] receive_pad = data[9:3];
  wire [67:3] q;
  /* verilator lint_off ASCRANGE */
  wire [2:8] reverse_q;
  /* verilator lint_on ASCRANGE */
  wire [6:0] receive_q;
  wire [67:3] sampled;
  logic [67:3] expected_sampled;

  wire unused_array_pad [3];

  unpacked_words_t array_en;
  unpacked_words_t array_data;
  wire unpacked_word_t array_pad [3:1];
  unpacked_words_t array_q;
  unpacked_words_t array_sampled;
  unpacked_words_t array_expected_sampled;
  wire [6:0] unpacked_matrix_pad [2:4][5:4];
  unpacked_matrix_t unpacked_matrix_q;
  wire array_receive_pad [3];
  wire array_receive_q [3];
  wire [6:0] array_fixed_pad [2:4];
  wire [6:0] array_fixed_q [2:4];
  wire [6:0] array_selected_pad [1:3];
  wire [6:0] array_selected_q [1:3];

  wide_io dut (
      .clk(clk),
      .en(en),
      .data(data),
      .pad(pad),
      .matrix_pad(matrix_pad),
      .reverse_pad(reverse_pad),
      .receive_pad(receive_pad),
      .q(q),
      .reverse_q(reverse_q),
      .receive_q(receive_q),
      .sampled(sampled),
      .cyc(cyc),
      .array_en(array_en),
      .array_data(array_data),
      .array_pad(array_pad),
      .array_q(array_q),
      .array_sampled(array_sampled),
      .unpacked_matrix_pad(unpacked_matrix_pad),
      .unpacked_matrix_q(unpacked_matrix_q),
      .array_receive_pad(array_receive_pad),
      .array_receive_q(array_receive_q),
      .array_fixed_pad(array_fixed_pad),
      .array_fixed_q(array_fixed_q),
      .array_selected_pad(array_selected_pad),
      .array_selected_q(array_selected_q),
      .unused_array_pad(unused_array_pad)
  );

  for (genvar i = 3; i <= 67; ++i) begin
    assign pad[i] = en[i] ? 1'bz : external_data[i];
  end
  for (genvar i = 1; i >= 0; --i) begin
    for (genvar j = 2; j <= 4; ++j) begin
      assign matrix_pad[i][j] = matrix_en[i][j] ? 1'bz : matrix_external[i][j];
    end
  end
  for (genvar i = 2; i <= 8; ++i) begin
    assign reverse_pad[i] = en[i+1] ? 1'bz : external_data[i+1];
    always @(negedge clk) `checkh(reverse_q[i], expected[i+1]);
  end

  always @(posedge clk) begin
    expected_sampled <= expected;
  end
  always @(negedge clk) begin
    `checkh(q, expected);
    `checkh(matrix_pad, matrix_expected);
    `checkh(receive_q, data[9:3]);
    `checkh(sampled, expected_sampled);
  end

  // Unpacked array ports use independent element and bit enables.
  for (genvar i = 1; i <= 3; ++i) begin
    assign array_en[i] = 65'h15555555555555555 ^ (65'(cyc) << (i * 7)) ^ {65{cyc[i]}};
    assign array_data[i] = 65'h123456789abcdef01 ^ (65'(cyc) << (i * 13)) ^ 65'(cyc + i);
    wire [67:3] external_data = ~array_data[i];
    wire [67:3] expected = (array_en[i] & array_data[i]) | (~array_en[i] & external_data);
    for (genvar b = 3; b <= 67; ++b) begin
      assign array_pad[i][b] = array_en[i][b] ? 1'bz : external_data[b];
    end
    always @(posedge clk) array_expected_sampled[i] <= expected;
    always @(negedge clk) begin
      `checkh(array_q[i], expected);
      `checkh(array_sampled[i], array_expected_sampled[i]);
    end
  end

  for (genvar i = 2; i <= 4; ++i) begin
    for (genvar j = 4; j <= 5; ++j) begin
      wire enable = cyc[i + j - 6];
      wire [6:0] value = 7'(cyc * (i + j));
      assign unpacked_matrix_pad[i][j] = enable ? 7'bz : ~value;
      always @(negedge clk) `checkh(unpacked_matrix_q[i][j], enable ? value : ~value);
    end
  end
  for (genvar i = 0; i < 3; ++i) begin
    assign array_receive_pad[i] = cyc[i];
    always @(negedge clk) begin
      `checkh(array_receive_q[i], cyc[i]);
      `checkh(array_receive_pad[i] === 1'bz, 1'b0);
    end
  end

  for (genvar i = 2; i <= 4; ++i) begin
    assign array_fixed_pad[i][6:3] = 4'(cyc + i);
    always @(negedge clk) `checkh(array_fixed_q[i], {4'(cyc + i), 3'(cyc ^ i)});
  end
  for (genvar i = 1; i <= 3; ++i) begin
    assign array_selected_pad[i] = i == 1 + cyc % 3 ? 7'bz : 7'(int'(cyc) + i + 17);
    always @(negedge clk)
      `checkh(array_selected_q[i], i == 1 + cyc % 3 ? 7'(cyc) : 7'(int'(cyc) + i + 17));
  end

  // Propagate the selected element's drive enable to a pulled-up destination.
  tri [6:0] array_source [3];
  tri1 [6:0] array_relay;
  wire [1:0] array_index = 2'(cyc % 3);
  wire [2:0] array_enable = cyc[2:0];
  wire [6:0] array_value = 7'(cyc * 19);
  for (genvar i = 0; i < 3; ++i) begin
    assign array_source[i] = array_enable[i] ? (array_value ^ 7'(i * 13)) : 7'bz;
  end
  assign array_relay = array_source[array_index];
  always @(negedge clk)
    `checkh(array_relay, array_enable[array_index] ? (array_value ^ 7'(int'(array_index) * 13)) : 7'h7f);

  // A child port's pullup must propagate to the connected array element.
  wire [6:0] array_pull_pad [2];
  array_pull_io array_pull_dut (.pad(array_pull_pad[0]));
  assign array_pull_pad[0] = cyc[0] ? array_value : 7'bz;
  assign array_pull_pad[1] = 7'(cyc + 17);
  always @(negedge clk) begin
    `checkh(array_pull_pad[0], cyc[0] ? array_value : 7'h7f);
    `checkh(array_pull_pad[1], 7'(cyc + 17));
  end

  // An element pull must preserve the tri1 default on all other elements and bits.
  tri1 [6:0] array_default_pull [2];
  array_pull_io array_default_pull_dut (.pad(array_default_pull[0]));
  tri1 [6:0] matrix_default_pull [2:4][5:4];
  array_pull_io #(.WIDTH(4)) matrix_default_pull_dut (.pad(matrix_default_pull[3][4][6:3]));
  for (genvar i = 0; i < 2; ++i) begin
    assign array_default_pull[i] = cyc[i] ? array_value : 7'bz;
    always @(negedge clk)
      `checkh(array_default_pull[i], cyc[i] ? array_value : 7'h7f);
  end
  for (genvar i = 2; i <= 4; ++i) begin
    for (genvar j = 4; j <= 5; ++j) begin
      assign matrix_default_pull[i][j] = cyc[i+j-6] ? array_value : 7'bz;
      always @(negedge clk)
        `checkh(matrix_default_pull[i][j], cyc[i+j-6] ? array_value : 7'h7f);
    end
  end

  // Preserve per-bit pulls through another hierarchy level and both array dimensions.
  wire [6:0] array_pull_matrix [2:4][5:4];
  array_pull_matrix_io array_pull_matrix_dut (.pad(array_pull_matrix));
  for (genvar i = 2; i <= 4; ++i) begin
    for (genvar j = 4; j <= 5; ++j) begin
      if ((i == 3 && j == 4) || i == 4) begin
        assign array_pull_matrix[i][j] = cyc[0] ? array_value : 7'bz;
        always @(negedge clk)
          `checkh(array_pull_matrix[i][j], cyc[0] ? array_value : (i == 3 ? 7'h78 : 7'h7f));
      end else begin
        assign array_pull_matrix[i][j] = ~array_value;
        always @(negedge clk) `checkh(array_pull_matrix[i][j], ~array_value);
      end
    end
  end

endmodule

module array_pull_io #(parameter WIDTH = 7) (inout tri1 [WIDTH-1:0] pad);
endmodule

module array_pull_down_io(inout tri0 [2:0] pad);
endmodule

module array_pull_pair_io(inout tri1 [6:0] pad [5:4]);
endmodule

module array_pull_matrix_io(inout wire [6:0] pad [2:4][5:4]);
  array_pull_io #(.WIDTH(4)) high_bits (.pad(pad[3][4][6:3]));
  array_pull_down_io low_bits (.pad(pad[3][4][2:0]));
  array_pull_pair_io whole_row (.pad(pad[4]));
endmodule

module tri_pad (
    inout wire pad,
    input wire ie,
    input wire oe,
    input wire to_pad,
    output wire from_pad
);

  assign pad = oe ? to_pad : 1'bz;
  assign from_pad = ie ? pad : 1'bz;
endmodule

module pad_binary (
    input wire pad_in,
    output wire pad_out,
    output wire pad_en,
    input wire ie,
    input wire oe,
    input wire to_pad,
    output from_pad_out,
    output wire from_pad_en
);

  assign pad_out = oe & to_pad;
  assign pad_en = oe;
  assign from_pad_out = ie & ((oe & to_pad) | pad_in);
  assign from_pad_en = ie;
endmodule

// Non-zero bounds, an ascending range, and a receive-only inout.
module wide_io (
    input clk,
    input [67:3] en,
    input [67:3] data,
    inout wire [67:3] pad,
    inout wire [1:0][4:2] matrix_pad,
    /* verilator lint_off ASCRANGE */
    inout wire [2:8] reverse_pad,
    /* verilator lint_on ASCRANGE */
    inout wire [6:0] receive_pad,
    output wire [67:3] q,
    /* verilator lint_off ASCRANGE */
    output wire [2:8] reverse_q,
    /* verilator lint_on ASCRANGE */
    output wire [6:0] receive_q,
    output logic [67:3] sampled,
    input [5:0] cyc,
    input unpacked_words_t array_en,
    input unpacked_words_t array_data,
    inout wire unpacked_words_t array_pad,
    inout wire [6:0] unpacked_matrix_pad [2:4][5:4],
    inout wire array_receive_pad [3],
    inout wire [6:0] array_fixed_pad [2:4],
    inout wire [6:0] array_selected_pad [1:3],
    output unpacked_words_t array_q,
    output unpacked_words_t array_sampled,
    output unpacked_matrix_t unpacked_matrix_q,
    output wire array_receive_q [3],
    output wire [6:0] array_fixed_q [2:4],
    output wire [6:0] array_selected_q [1:3],
    inout wire unused_array_pad [3]
);
  for (genvar i = 3; i <= 67; ++i) begin
    assign pad[i] = en[i] ? data[i] : 1'bz;
  end
  for (genvar i = 1; i >= 0; --i) begin
    for (genvar j = 2; j <= 4; ++j) begin
      assign matrix_pad[i][j] = en[i*3+j+1] ? data[i*3+j+1] : 1'bz;
    end
  end
  for (genvar i = 2; i <= 8; ++i) begin
    assign reverse_pad[i] = en[i+1] ? data[i+1] : 1'bz;
  end
  assign q = pad;
  assign reverse_q = reverse_pad;
  assign receive_q = receive_pad;
  always @(posedge clk) sampled <= pad;
  for (genvar i = 1; i <= 3; ++i) begin
    for (genvar b = 3; b <= 67; ++b) begin
      assign array_pad[i][b] = array_en[i][b] ? array_data[i][b] : 1'bz;
    end
  end
  for (genvar i = 2; i <= 4; ++i) begin
    for (genvar j = 4; j <= 5; ++j) begin
      if (i == 2 && j == 4) begin
        wire [6:0] element_data = 7'(cyc * (i + j));
        for (genvar b = 0; b < 7; ++b) begin
          io elem (.A(element_data[b]), .OE(cyc[0]), .Z(unpacked_matrix_pad[i][j][b]), .Y());
        end
      end else begin
        assign unpacked_matrix_pad[i][j] = cyc[i + j - 6] ? 7'(cyc * (i + j)) : 7'bz;
      end
    end
  end
  for (genvar i = 2; i <= 4; ++i) begin
    assign array_fixed_pad[i][2:0] = 3'(cyc ^ i);
  end
  assign array_selected_pad[1 + cyc % 3] = 7'(cyc);
  assign array_fixed_q = array_fixed_pad;
  assign array_selected_q = array_selected_pad;
  assign array_q = array_pad;
  assign unpacked_matrix_q = unpacked_matrix_pad;
  assign array_receive_q = array_receive_pad;
  always @(posedge clk) array_sampled <= array_pad;
endmodule
