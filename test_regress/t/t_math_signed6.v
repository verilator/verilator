// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Iztok Jeras.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

  module t (/*AUTOARG*/);

   // signed source
   logic   signed  [8-1:0] src;

   // destination structure
   struct packed {
     logic   signed [16-1:0] s;
     logic unsigned [16-1:0] u;
   } dst;

   initial begin
      // bug882
      // verilator lint_off WIDTH
      src = 8'sh05;
      dst = '{s: src, u: src};
      `checkh (dst.s, 16'h0005);
      `checkh (dst.u, 16'h0005);

      src = 8'shf5;
      dst = '{s: src, u: src};
      `checkh (dst.s, 16'hfff5);
      `checkh (dst.u, 16'hfff5);
      // verilator lint_on WIDTH

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
