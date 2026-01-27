// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t(
   input clk
  );
  int cyc=1;

  // Instantiate the primitive gates to be tested.
  and g_and(o_and, i_and1, i_and2, i_and3),
   g2_and(o2_and, i_and1, i_and2, i_and3);
  not g_not(o_not1, o_not2, i_not1),
   g2_not(o2_not1, o_not2, i_not1);
  nor g_nor(o_nor, i_nor1, i_nor2, i_nor3),
   g2_nor(o2_nor, i_nor1, i_nor2, i_nor3);
  or g_or(o_or, i_or1, i_or2, i_or3),
   g2_or(o2_or, i_or1, i_or2, i_or3);
  nand g_nand(o_nand, i_nand1, i_nand2, i_nand3),
   g2_nand(o2_nand, i_nand1, i_nand2, i_nand3);
  xor g_xor(o_xor, i_xor1, i_xor2, i_xor3),
   g2_xor(o2_xor, i_xor1, i_xor2, i_xor3);
  xnor g_xor(o_xnor, i_xnor1, i_xnor2, i_xnor3),
   g2_xor(o2_xnor, i_xnor1, i_xnor2, i_xnor3);
  buf g_buf(o_buf1, o_buf2, i_buf1),
   g2_buf(o2_buf1, o_buf2, i_buf1);
  bufif0 g_bufif0(o_bufif0, i_bufif01, i_bufif02),
   g2_bufif0(o2_bufif0, i_bufif01, i_bufif02);
  bufif1 g_bufif1(o_bufif1, i_bufif11, i_bufif12),
   g2_bufif1(o2_bufif1, i_bufif11, i_bufif12);
  notif0 g_notif0(o_notif0, i_notif01, i_notif02),
   g2_notif0(o2_notif0, i_notif01, i_notif02);
  notif1 g_notif1(o_notif1, i_notif11, i_notif12),
   g2_notif1(o2_notif1, i_notif11, i_notif12);

  // Generate random data for inputs
  reg  rd_data1, rd_data2, rd_data3;
  always @(posedge clk) begin
    rd_data1 = 1'($random);
    rd_data2 = 1'($random);
    rd_data3 = 1'($random);
  end

  // Assign the input of primitive gates.
`default_nettype none
  assign i_and1 = rd_data1;
  assign i_and2 = rd_data2;
  assign i_and3 = rd_data3;

  assign i_not1 = rd_data1;

  assign i_nor1 = rd_data1;
  assign i_nor2 = rd_data2;
  assign i_nor3 = rd_data3;

  assign i_or1 = rd_data1;
  assign i_or2 = rd_data2;
  assign i_or3 = rd_data3;

  assign i_nand1 = rd_data1;
  assign i_nand2 = rd_data2;
  assign i_nand3 = rd_data3;

  assign i_xor1 = rd_data1;
  assign i_xor2 = rd_data2;
  assign i_xor3 = rd_data3;

  assign i_xnor1 = rd_data1;
  assign i_xnor2 = rd_data2;
  assign i_xnor3 = rd_data3;

  assign i_buf1 = rd_data1;

  assign i_bufif01 = rd_data1;
  assign i_bufif02 = rd_data2;

  assign i_bufif11 = rd_data1;
  assign i_bufif12 = rd_data2;

  assign i_notif01 = rd_data1;
  assign i_notif02 = rd_data2;

  assign i_notif11 = rd_data1;
  assign i_notif12 = rd_data2;

  // Check the outputs of the gate instances
  always @(negedge clk) begin
    if (o_and !== (i_and1 & i_and2 & i_and3)) $stop;
    if ((o_not1 !== ~i_not1) || (o_not2 != ~i_not1)) $stop;
    if (o_nor !== !(i_nor1 | i_nor2 | i_nor3)) $stop;
    if (o_or !== (i_or1 | i_or2 | i_or3)) $stop;
    if (o_nand !== !(i_nand1 & i_nand2 & i_nand3)) $stop;
    if (o_xor !== (i_xor1 ^ i_xor2 ^ i_xor3)) $stop;
    if (o_xnor !== !(i_xnor1 ^ i_xnor2 ^ i_xnor3)) $stop;
    if ((o_buf1 !== i_buf1) || (o_buf2 !== i_buf1)) $stop;
    if (!(o_bufif0 == (i_bufif01 & !i_bufif02))) $stop;
    if (!(o_bufif1 == (i_bufif11 & i_bufif12))) $stop;
    if (!(o_notif0 == (!i_notif01 & !i_notif02))) $stop;
    if (!(o_notif1 == (!i_notif11 & i_notif12))) $stop;
    `checkh(o2_and, o2_and);
    `checkh(o2_not1, o2_not1);
    `checkh(o2_nor, o2_nor);
    `checkh(o2_or, o2_or);
    `checkh(o2_nand, o2_nand);
    `checkh(o2_xor, o2_xor);
    `checkh(o2_xnor, o2_xnor);
    `checkh(o2_buf1, o2_buf1);
    `checkh(o2_bufif0, o2_bufif0);
    `checkh(o2_bufif1, o2_bufif1);
    `checkh(o2_notif0, o2_notif0);
    `checkh(o2_notif1, o2_notif1);
  end

  always @(posedge clk) begin
    cyc = cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
