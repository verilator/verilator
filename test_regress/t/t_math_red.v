// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc = 0;

   reg [67:0]    r;

   wire and_reduce = &r;
   wire or_reduce = |r;
   wire xor_reduce = ^r;
   wire xnor_reduce = ~^r;
   wire check_equal = r == 68'hffff_ffff_ffff_ffff_f;

   always @(posedge clk) begin
`ifdef TEST_VERBOSE
      $display("cyc=%0d, r = %x, and_reduce = %x, or=%x xor=%x check_equal = %x",
               cyc, r, and_reduce, or_reduce, xor_reduce, check_equal);
`endif
      cyc <= cyc + 1;
      if (cyc == 1) begin
         r <= 68'd0;
      end
      else if (cyc == 10) begin
         `checkh(r, 68'h0000_0000_0000_0000_0);
         `checkh(and_reduce, '0);
         `checkh(or_reduce, '0);
         `checkh(xor_reduce, '0);
         `checkh(xnor_reduce, '1);
         r <= 68'hffff_ffff_ffff_ffff_e;
      end
      else if (cyc == 11) begin
         `checkh(r, 68'hffff_ffff_ffff_ffff_e);
         `checkh(and_reduce, '0);
         `checkh(or_reduce, '1);
         `checkh(xor_reduce, '1);
         `checkh(xnor_reduce, '0);
         r <= 68'hffff_ffff_ffff_ffff_f;
      end
      else if (cyc == 12) begin
         `checkh(r, 68'hffff_ffff_ffff_ffff_f);
         `checkh(and_reduce, '1);
         `checkh(or_reduce, '1);
         `checkh(xor_reduce, '0);
         `checkh(xnor_reduce, '1);
      end
      else if (cyc == 90) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         r <= 68'd0;
      end
   end
endmodule
