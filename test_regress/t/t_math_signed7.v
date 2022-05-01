// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg alu_ltu, alu_lts;
   logic [3:0] in_op1;
   logic [3:0] in_op2;


   reg aaa_ltu, aaa_lts;
      always @(posedge clk) begin
         in_op1 = 4'sb1110;
         in_op2 =  4'b0010;
         aaa_ltu = in_op1 < in_op2;
         // bug999
         aaa_lts = $signed(in_op1) < $signed(in_op2);
         `checkh (aaa_ltu, 1'b0);
         `checkh (aaa_lts, 1'b1);
      end

   generate if (1) begin
      always @(posedge clk) begin
         in_op1 = 4'sb1110;
         in_op2 =  4'b0010;
         alu_ltu = in_op1 < in_op2;
         // bug999
         alu_lts = $signed(in_op1) < $signed(in_op2);
         `checkh (alu_ltu, 1'b0);
         `checkh (alu_lts, 1'b1);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
   endgenerate
endmodule
