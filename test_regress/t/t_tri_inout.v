// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Lane Brooks
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0x exp=%0x\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module top (input A, input B, input SEL, input clk, output Y1, output Y2, output Z, output done);
  io   io1(.A(A), .OE( SEL), .Z(Z), .Y(Y1));
  pass io2(.A(B), .OE(!SEL), .Z(Z), .Y(Y2));
  assign Z = 1'bz;

  pad_checker u_pad_checker(.clk(clk), .done(done));
endmodule

module pass (input A, input OE, inout Z, output Y);
  io_noinline io(.A(A), .OE(OE), .Z(Z), .Y(Y));
  assign Z = 1'bz;
endmodule

module io (input A, input OE, inout Z, output Y);
  assign Z = (OE) ? A : 1'bz;
  assign Y = Z;
  assign Z = 1'bz;
endmodule

module io_noinline (input A, input OE, inout Z, output Y);
  /*verilator no_inline_module*/
  assign Z = (OE) ? A : 1'bz;
  assign Y = Z;
  assign Z = 1'bz;
endmodule


module pad_checker(input wire clk, output wire done);
  wire tri_pad;
  reg [1:0] ie = '0;
  reg [1:0] oe = '0;
  reg [1:0] in = '0;
  wire out_0, out_1;

  tri_pad u_pad0(.pad(tri_pad), .ie(ie[0]), .oe(oe[0]), .to_pad(in[0]), .from_pad(out_0));
  tri_pad u_pad1(.pad(tri_pad), .ie(ie[1]), .oe(oe[1]), .to_pad(in[1]), .from_pad(out_1));

  wire bin_pad_in_0, bin_pad_in_1;
  wire bin_pad_01, bin_pad_10;
  wire bin_pad_en_01, bin_pad_en_10;
  wire bin_from_pad_out_0, bin_from_pad_out_1;
  wire bin_from_pad_en_0, bin_from_pad_en_1;

  // Expectation model that simulates how Verilator solves tri-state
  pad_binary u_pad_bin_0(.pad_in(bin_pad_in_0),
                    .pad_out(bin_pad_01),
                    .pad_en(bin_pad_en_01),
                    .ie(ie[0]), .oe(oe[0]),
                    .to_pad(in[0]),
                    .from_pad_out(bin_from_pad_out_0),
                    .from_pad_en(bin_from_pad_en_0));

  pad_binary u_pad_bin_1(.pad_in(bin_pad_in_1),
                    .pad_out(bin_pad_10),
                    .pad_en(bin_pad_en_10),
                    .ie(ie[1]),
                    .oe(oe[1]),
                    .to_pad(in[1]),
                    .from_pad_out(bin_from_pad_out_1),
                    .from_pad_en(bin_from_pad_en_1));

  assign bin_pad_in_0 = (bin_pad_en_10 & bin_pad_10) | (bin_pad_en_01 & bin_pad_01);
  assign bin_pad_in_1 = (bin_pad_en_01 & bin_pad_01) | (bin_pad_en_10 & bin_pad_10);


  logic done_reg = 0;
  assign done = done_reg;
  always @(posedge clk) begin
    if ({ie, oe, in} == 6'b111111) begin
      done_reg <= 1'b1;
    end else begin
      if (out_0 != bin_from_pad_out_0) begin
        $display("ie:%b oe:%b in:%b out0 act:%b exp:%b", ie[0], oe[0], in[0], out_0, bin_from_pad_out_0);
        $stop;
      end
      if (out_1 != bin_from_pad_out_1) begin
        $display("ie:%b oe:%b in:%b out1 act:%b exp:%b", ie[1], oe[1], in[1], out_1, bin_from_pad_out_1);
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
  wire [1:0][4:2] matrix_expected
      = (matrix_en & matrix_data) | (~matrix_en & matrix_external);
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
      .sampled(sampled)
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

endmodule

module tri_pad(inout wire pad, input wire ie, input wire oe, input wire to_pad, output wire from_pad);

  assign pad = oe ? to_pad : 1'bz;
  assign from_pad = ie ? pad : 1'bz;
endmodule

module pad_binary(input wire pad_in,
            output wire pad_out,
            output wire pad_en,
            input wire ie,
            input wire oe,
            input wire to_pad,
            output from_pad_out,
            output wire from_pad_en);

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
    output logic [67:3] sampled
);
  for (genvar i = 3; i <= 67; ++i) begin
    assign pad[i] = en[i] ? data[i] : 1'bz;
  end
  for (genvar i = 1; i >= 0; --i) begin
    for (genvar j = 2; j <= 4; ++j) begin
      assign matrix_pad[i][j] = en[i * 3 + j + 1] ? data[i * 3 + j + 1] : 1'bz;
    end
  end
  for (genvar i = 2; i <= 8; ++i) begin
    assign reverse_pad[i] = en[i+1] ? data[i+1] : 1'bz;
  end
  assign q = pad;
  assign reverse_q = reverse_pad;
  assign receive_q = receive_pad;
  always @(posedge clk) sampled <= pad;
endmodule
