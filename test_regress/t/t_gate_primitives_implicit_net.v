// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;
   int   cyc=1;

   // Instantiate the primitive gates to be tested.
   and g_and(o_and, i_and1, i_and2, i_and3);
   not g_not(o_not1, o_not2, i_not1);
   nor g_nor(o_nor, i_nor1, i_nor2, i_nor3);
   or g_or(o_or, i_or1, i_or2, i_or3);
   nand g_nand(o_nand, i_nand1, i_nand2, i_nand3);
   xor g_xor(o_xor, i_xor1, i_xor2, i_xor3);
   xnor g_xor(o_xnor, i_xnor1, i_xnor2, i_xnor3);
   buf g_buf(o_buf1, o_buf2, i_buf1);
   bufif0 g_bufif0(o_bufif0, i_bufif01, i_bufif02);
   bufif1 g_bufif1(o_bufif1, i_bufif11, i_bufif12);
   notif0 g_notif0(o_notif0, i_notif01, i_notif02);
   notif1 g_notif1(o_notif1, i_notif11, i_notif12);

   // Generate random data for inputs
   reg   rd_data1, rd_data2, rd_data3;
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
   end

   always @(posedge clk) begin
      cyc = cyc + 1;
      if (cyc == 100) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
