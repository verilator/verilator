// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkb(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='b%x exp='b%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t(
clk
/*AUTOARG*/);
  input clk;
  wor [3:0] ptrior1;
  trior [3:0] ptrior2;
  wand [3:0] ptriand1;
  triand [3:0] ptriand2;
  wire [3:0] z1;
  wire [3:0] z2;
  wire [3:0] tri_z1;
  wire [3:0] tri_z2;
  logic [3:0] x;
  logic [3:0] y;
  logic [3:0] tri_x;
  logic [3:0] tri_y;
  logic [3:0] tri_x_dat;
  logic [3:0] tri_y_dat;
  logic [3:0] tri_x_en;
  logic [3:0] tri_y_en;
  assign ptrior1 = x & y;
  assign ptrior1 = x + y;
  assign ptrior2 = tri_x & tri_y;
  assign ptrior2 = tri_x + tri_y;
  assign ptriand1 = x & y;
  assign ptriand1 = x + y;
  assign ptriand2 = tri_x & tri_y;
  assign ptriand2 = tri_x + tri_y;
  assign z1 = (x & y) | (x + y);
  assign z2 = (x & y) & (x + y);
  assign tri_z1 = (tri_x & tri_y) | (tri_x + tri_y);
  assign tri_z2 = (tri_x & tri_y) & (tri_x + tri_y);
  integer cyc = 0;
  integer xz_index = 0;
  integer xz_num = 0;
  integer i;
  assign tri_x[0] = tri_x_en[0] ? tri_x_dat[0] : 1'bz;
  assign tri_x[1] = tri_x_en[1] ? tri_x_dat[1] : 1'bz;
  assign tri_x[2] = tri_x_en[2] ? tri_x_dat[2] : 1'bz;
  assign tri_x[3] = tri_x_en[3] ? tri_x_dat[3] : 1'bz;
  assign tri_y[0] = tri_y_en[0] ? tri_y_dat[0] : 1'bz;
  assign tri_y[1] = tri_y_en[1] ? tri_y_dat[1] : 1'bz;
  assign tri_y[2] = tri_y_en[2] ? tri_y_dat[2] : 1'bz;
  assign tri_y[3] = tri_y_en[3] ? tri_y_dat[3] : 1'bz;
  // Constant drivers are merged like any other driver
  wor [4:0] c_wor;
  assign c_wor = 5'b00001;
  assign c_wor = 5'b00100;
  wand [4:0] c_wand;
  assign c_wand = 5'b10111;
  assign c_wand = 5'b11101;
  assign c_wand = 5'b11110;
  trior [4:0] c_trior;
  assign c_trior = {1'b0, x};
  assign c_trior = 5'b10010;
  triand [4:0] c_triand;
  assign c_triand = 5'b01101;
  assign c_triand = {1'b1, y};
  wire [4:0] c_trior_exp = {1'b0, x} | 5'b10010;
  wire [4:0] c_triand_exp = {1'b1, y} & 5'b01101;
  // Bit/part selects of wired nets resolve, not last-write-wins
  wor [2:0] s_wor;
  assign s_wor[0] = x[0];
  assign s_wor[0] = y[0];
  assign s_wor[2:1] = x[2:1];
  assign s_wor[2:1] = y[2:1];
  wand [2:0] s_wand;
  assign s_wand[0] = x[0];
  assign s_wand[0] = y[0];
  assign s_wand[2:1] = x[2:1];
  assign s_wand[2:1] = y[2:1];
  trior [2:0] s_trior;
  assign s_trior[0] = x[0];
  assign s_trior[0] = y[0];
  triand [2:0] s_triand;
  assign s_triand[0] = x[0];
  assign s_triand[0] = y[0];
  // Different bits of the same net stay independent
  wor [1:0] s_bits;
  assign s_bits[0] = x[0];
  assign s_bits[1] = y[0];
  // Constant bit-selects, including two bits that are both 1
  wor [1:0] c_sel_wor;
  assign c_sel_wor[0] = 1'b1;
  assign c_sel_wor[0] = 1'b0;
  assign c_sel_wor[1] = 1'b1;
  wand [1:0] c_sel_wand;
  assign c_sel_wand[0] = 1'b1;
  assign c_sel_wand[0] = 1'b0;
  assign c_sel_wand[1] = 1'b1;
  assign c_sel_wand[1] = 1'b1;
  // Unpacked array element of a wired net
  wor u_wor [1:0];
  assign u_wor[0] = x[0];
  assign u_wor[0] = y[0];
  // Constant part-select of a wider packed net, and unpacked array of vectors
  wor [4:0] c_wor_slice;
  assign c_wor_slice[2:0] = 3'b001;
  assign c_wor_slice[2:0] = 3'b100;
  wor [4:0] c_wor_array [2:0];
  assign c_wor_array[1] = 5'b00001;
  assign c_wor_array[1] = 5'b00100;
  // Overlapping packed selects resolve per bit, not last-write-wins
  wor [3:0] o_ov;
  assign o_ov[1:0] = x[1:0];
  assign o_ov[0] = y[0];
  wand [3:0] a_ov;
  assign a_ov[1:0] = x[1:0];
  assign a_ov[0] = y[0];
  trior [1:0] t_ov;
  assign t_ov[1:0] = x[1:0];
  assign t_ov[0] = y[0];
  triand [1:0] d_ov;
  assign d_ov[1:0] = x[1:0];
  assign d_ov[0] = y[0];
  wor [1:0] o_wb;
  assign o_wb = x[1:0];
  assign o_wb[1] = y[0];
  wand [1:0] a_wb;
  assign a_wb = x[1:0];
  assign a_wb[0] = y[0];
  // Overlap plus a disjoint bit must not fill or redrive that bit
  wor [3:0] o_hi;
  assign o_hi[1:0] = x[1:0];
  assign o_hi[0] = y[0];
  assign o_hi[3] = x[2];
  wand [3:0] a_hi;
  assign a_hi[1:0] = x[1:0];
  assign a_hi[0] = y[0];
  assign a_hi[3] = x[2];
  wor [3:0] o_mid;
  assign o_mid[3:2] = x[1:0];
  assign o_mid[2] = y[0];
  assign o_mid[0] = y[1];
  wand [3:0] a_mid;
  assign a_mid[3:2] = x[1:0];
  assign a_mid[2] = y[0];
  assign a_mid[0] = y[1];
  // Non-zero and ascending packed bounds
  wor [3:1] nz_wor;
  assign nz_wor[1] = x[0];
  assign nz_wor[1] = y[0];
  assign nz_wor[3:2] = x[3:2];
  assign nz_wor[3:2] = y[3:2];
  wor [3:1] nz_ov;
  assign nz_ov[2:1] = x[1:0];
  assign nz_ov[1] = y[0];
  // verilator lint_off ASCRANGE
  wor [0:3] asc_wor;
  // verilator lint_on ASCRANGE
  assign asc_wor[0] = x[0];
  assign asc_wor[0] = y[0];
  assign asc_wor[3] = x[1];
  assign asc_wor[3] = y[1];
  // Wider than 64 bits, select crossing the word boundary at bit 64
  wor [69:0] w_wide;
  assign w_wide[66:62] = {x, y[0]};
  assign w_wide[64] = y[1];
  assign w_wide[69] = x[0];
  wand [69:0] a_wide;
  assign a_wide[66:62] = {x, y[0]};
  assign a_wide[64] = y[1];
  assign a_wide[69] = x[0];
  // Strength on a wired-net select is accepted and merged
  wor [1:0] st_wor;
  assign (weak0, weak1) st_wor[0] = x[0];
  assign (weak0, weak1) st_wor[0] = y[0];
  wire s_wor_exp0 = x[0] | y[0];
  wire [1:0] s_wor_exp21 = x[2:1] | y[2:1];
  wire s_wand_exp0 = x[0] & y[0];
  wire [1:0] s_wand_exp21 = x[2:1] & y[2:1];
  wire s_trior_exp0 = x[0] | y[0];
  wire s_triand_exp0 = x[0] & y[0];
  wire s_bits_exp0 = x[0];
  wire s_bits_exp1 = y[0];
  wire u_wor_exp0 = x[0] | y[0];
  wire [1:0] o_ov_exp = {x[1], x[0] | y[0]};
  wire [1:0] a_ov_exp = {x[1], x[0] & y[0]};
  wire [1:0] o_wb_exp = {x[1] | y[0], x[0]};
  wire [1:0] a_wb_exp = {x[1], x[0] & y[0]};
  wire [3:0] o_hi_exp = {x[2], 1'b0, x[1], x[0] | y[0]};
  wire [3:0] a_hi_exp = {x[2], 1'b0, x[1], x[0] & y[0]};
  wire [3:0] o_mid_exp = {x[1], x[0] | y[0], 1'b0, y[1]};
  wire [3:0] a_mid_exp = {x[1], x[0] & y[0], 1'b0, y[1]};
  wire [1:0] nz_wor_exp32 = x[3:2] | y[3:2];
  wire [1:0] nz_ov_exp = {x[1], x[0] | y[0]};
  wire asc_wor_exp3 = x[1] | y[1];
  wire [4:0] w_wide_exp = {x[3:2], x[1] | y[1], x[0], y[0]};
  wire [4:0] a_wide_exp = {x[3:2], x[1] & y[1], x[0], y[0]};
  always @ (posedge clk) begin
    cyc <= cyc + 1;
    x = {$random}[3:0];
    y = {$random}[3:0];
    tri_x_dat = {$random}[3:0];
    tri_y_dat = {$random}[3:0];
    tri_x_en = {$random}[3:0];
    tri_y_en = {$random}[3:0];
    `checkb(ptrior1, z1);
    `checkb(ptrior2, tri_z1);
    `checkb(ptriand1, z2);
    `checkb(ptriand2, tri_z2);
    `checkb(c_wor, 5'b00101);
    `checkb(c_wand, 5'b10100);
    `checkb(c_trior, c_trior_exp);
    `checkb(c_triand, c_triand_exp);
    `checkb(s_wor[0], s_wor_exp0);
    `checkb(s_wor[2:1], s_wor_exp21);
    `checkb(s_wand[0], s_wand_exp0);
    `checkb(s_wand[2:1], s_wand_exp21);
    `checkb(s_trior[0], s_trior_exp0);
    `checkb(s_triand[0], s_triand_exp0);
    `checkb(s_bits[0], s_bits_exp0);
    `checkb(s_bits[1], s_bits_exp1);
    `checkb(c_sel_wor, 2'b11);
    `checkb(c_sel_wand, 2'b10);
    `checkb(u_wor[0], u_wor_exp0);
    `checkb(c_wor_slice[2:0], 3'b101);
    `checkb(c_wor_array[1], 5'b00101);
    `checkb(o_ov[1:0], o_ov_exp);
    `checkb(a_ov[1:0], a_ov_exp);
    `checkb(t_ov, o_ov_exp);
    `checkb(d_ov, a_ov_exp);
    `checkb(o_wb, o_wb_exp);
    `checkb(a_wb, a_wb_exp);
    `checkb(o_hi, o_hi_exp);
    `checkb(a_hi, a_hi_exp);
    `checkb(o_mid, o_mid_exp);
    `checkb(a_mid, a_mid_exp);
    `checkb(nz_wor[1], s_wor_exp0);
    `checkb(nz_wor[3:2], nz_wor_exp32);
    `checkb(nz_ov[2:1], nz_ov_exp);
    `checkb(asc_wor[0], s_wor_exp0);
    `checkb(asc_wor[3], asc_wor_exp3);
    `checkb(w_wide[66:62], w_wide_exp);
    `checkb(w_wide[69], x[0]);
    `checkb(w_wide[68:67], 2'b00);
    `checkb(a_wide[66:62], a_wide_exp);
    `checkb(a_wide[69], x[0]);
    `checkb(a_wide[68:67], 2'b00);
    `checkb(st_wor[0], s_wor_exp0);
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
