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
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
