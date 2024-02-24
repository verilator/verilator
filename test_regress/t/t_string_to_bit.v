// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;

   string str0;
   string str1;
   string str2;

   typedef bit [31:0] bit_t;
   typedef logic [31:0] logic_t;
   typedef bit [55:0] quad_t;
   typedef bit [87:0] wide_t;

   bit_t bdata[3];
   bit_t ldata[3];
   quad_t qdata[3];
   wide_t wdata[3];

   initial begin
      str0 = "sm";
      str1 = "medium";
      str2 = "veryverylongwilltruncate";
      bdata[0] = bit_t'(str0);
      bdata[1] = bit_t'(str1);
      bdata[2] = bit_t'(str2);
      `checks(bdata[0], "sm");
      `checks(bdata[1], "dium");
      `checks(bdata[2], "cate");
      if (bdata[0] != 32'h0000736d) $stop;
      if (bdata[1] != 32'h6469756d) $stop;
      ldata[0] = logic_t'(str0);
      ldata[1] = logic_t'(str1);
      ldata[2] = logic_t'(str2);
      `checks(ldata[0], "sm");
      `checks(ldata[1], "dium");
      `checks(ldata[2], "cate");
      qdata[0] = quad_t'(str0);
      qdata[1] = quad_t'(str1);
      qdata[2] = quad_t'(str2);
      `checks(qdata[0], "sm");
      `checks(qdata[1], "medium");
      `checks(qdata[2], "runcate");
      wdata[0] = wide_t'(str0);
      wdata[1] = wide_t'(str1);
      wdata[2] = wide_t'(str2);
      `checks(wdata[0], "sm");
      `checks(wdata[1], "medium");
      `checks(wdata[2], "illtruncate");
   end

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         str0 = "z";
         str1 = "zmedi";
         str2 = "ziggylonglonglongtruncate";
      end
      else if (cyc == 2) begin
         bdata[0] = bit_t'(str0);
         bdata[1] = bit_t'(str1);
         bdata[2] = bit_t'(str2);
         ldata[0] = logic_t'(str0);
         ldata[1] = logic_t'(str1);
         ldata[2] = logic_t'(str2);
         qdata[0] = quad_t'(str0);
         qdata[1] = quad_t'(str1);
         qdata[2] = quad_t'(str2);
         wdata[0] = wide_t'(str0);
         wdata[1] = wide_t'(str1);
         wdata[2] = wide_t'(str2);
      end
      else if (cyc == 3) begin
         `checks(bdata[0], "z");
         `checks(bdata[1], "medi");
         `checks(bdata[2], "cate");
         `checks(ldata[0], "z");
         `checks(ldata[1], "medi");
         `checks(ldata[2], "cate");
         `checks(qdata[0], "z");
         `checks(qdata[1], "zmedi");
         `checks(qdata[2], "runcate");
         `checks(wdata[0], "z");
         `checks(wdata[1], "zmedi");
         `checks(wdata[2], "ongtruncate");
      end
      //
      else if (cyc==99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
