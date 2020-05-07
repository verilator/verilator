// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv));; end while(0);

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   int   cyc;

   int vr;
   int va[2];

`ifdef T_NOINLINE
   // verilator no_inline_module
`endif

   //====

   task fun(ref int r, const ref int c);
`ifdef T_NOINLINE
      // verilator no_inline_task
`endif
      `checkh(c, 32'h1234);
      r = 32'h4567;
   endtask

   initial begin
      int ci;
      int ri;
      ci = 32'h1234;
      fun(ri, ci);
      `checkh(ri, 32'h4567);
   end

   //====

   task fun_array(ref int af[2], const ref int cf[2]);
`ifdef T_NOINLINE
      // verilator no_inline_task
`endif
      `checkh(cf[0], 32'h1234);
      `checkh(cf[1], 32'h2345);
      af[0] = 32'h5678;
      af[1] = 32'h6789;
   endtask
   // Not checkint - element of unpacked array

   initial begin
      int ca[2];
      int ra[2];
      ca[0] = 32'h1234;
      ca[1] = 32'h2345;
      fun_array(ra, ca);
      `checkh(ra[0], 32'h5678);
      `checkh(ra[1], 32'h6789);
   end

   //====

   sub sub(.clk, .vr, .va);

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 0) begin
         vr <= 32'h789;
         va[0] <= 32'h89a;
         va[1] <= 32'h9ab;
      end
      else if (cyc == 2) begin
         `checkh(vr, 32'h987);
         `checkh(va[0], 32'ha98);
         `checkh(va[1], 32'ha9b);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module sub(input clk, ref int vr, ref int va[2]);

   always @(posedge clk) begin
      vr <= 32'h987;
      va[0] <= 32'ha98;
      va[1] <= 32'ha9b;
   end

endmodule
