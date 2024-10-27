// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   typedef struct {
      int b[$];
   } st_t;

   typedef struct {
      int v;
   } st_in_t;

   function automatic st_t bar();
      // verilator no_inline_task
      for (int i = 0; i < 4; ++i) begin
         bar.b.push_back(i);
      end
   endfunction // bar

   st_t res;
   st_in_t q[$];

   initial begin
      res = bar();
      `checkd(res.b[0], 0);
      `checkd(res.b[1], 1);
      `checkd(res.b[2], 2);
      `checkd(res.b[3], 3);

      q.push_back(st_in_t'{15});
      q[0].v++;
      `checkd(q[0].v, 16);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
