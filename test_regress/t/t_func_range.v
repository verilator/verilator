// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   // verilator lint_off WIDTH

`define INT_RANGE     31:0
`define INT_RANGE_MAX 31
`define VECTOR_RANGE 63:0

   reg [`INT_RANGE] stashb, stasha, stashn, stashm;

   function [`VECTOR_RANGE] copy_range;
      input [`VECTOR_RANGE]  y;
      input [`INT_RANGE] b;
      input [`INT_RANGE] a;

      input [`VECTOR_RANGE]  x;
      input [`INT_RANGE] n;
      input [`INT_RANGE] m;

      begin
         copy_range = y;
         stashb = b;
         stasha = a;
         stashn = n;
         stashm = m;
      end
   endfunction

   parameter DATA_SIZE = 16;
   parameter NUM_OF_REGS = 32;

   reg [NUM_OF_REGS*DATA_SIZE-1 : 0] memread_rf;
   reg [DATA_SIZE-1:0]                memread_rf_reg;
   always @(memread_rf) begin : memread_convert
      memread_rf_reg = copy_range('d0, DATA_SIZE-'d1, DATA_SIZE-'d1,   memread_rf,
                                  DATA_SIZE-'d1, DATA_SIZE-'d1);
   end

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            memread_rf = 512'haa;
         end
         if (cyc==3) begin
            if (stashb != 'd15) $stop;
            if (stasha != 'd15) $stop;
            if (stashn != 'd15) $stop;
            if (stashm != 'd15) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
