// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc=0;

   integer i;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      begin
         // Wildcard
         string a [*];
         int k;
         string v;

         a[32'd1234] = "fooed";
         a[4'd3] = "bared";
         i = a.num(); `checkh(i, 2);
         i = a.size(); `checkh(i, 2);
         v = a[32'd1234]; `checks(v, "fooed");
         v = a[4'd3]; `checks(v, "bared");
         i = a.exists("baz"); `checkh(i, 0);
         i = a.exists(4'd3); `checkh(i, 1);
         i = a.first(k); `checkh(i, 1); `checks(k, 4'd3);
         i = a.next(k); `checkh(i, 1); `checks(k, 32'd1234);
         i = a.next(k); `checkh(i, 0);
         i = a.last(k); `checkh(i, 1); `checks(k, 32'd1234);
         i = a.prev(k); `checkh(i, 1); `checks(k, 4'd3);
         i = a.prev(k); `checkh(i, 0);
         a.delete(4'd3);
         i = a.size(); `checkh(i, 1);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
