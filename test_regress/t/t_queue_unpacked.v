// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   typedef string sarray_t[2];
   typedef sarray_t q_sarray_t[$];

   typedef bit [95:0] wide_t;
   typedef wide_t warray_t[2];
   typedef warray_t q_warray_t[$];

   initial begin
      begin
         q_sarray_t iq;
         sarray_t a;
         sarray_t b0;
         sarray_t b1;

         a[0] = "hello";
         a[1] = "world";
         iq.push_back(a);
         a[0] = "bye";
         a[1] = "world";
         iq.push_back(a);

         b0 = iq[0];
         b1 = iq[1];
         `checks(b0[0], "hello");
         `checks(b0[1], "world");
         `checks(b1[0], "bye");
         `checks(b1[1], "world");
      end

`ifndef verilator
      // Need wide conversion into VlUnpacked types

      // If we convert all arrays to VlUnpacked it works, so we need to track
      // data types and insert conversions perhaps in V3Cast, but we currently
      // don't know the output datatypes, so work needed.
      begin
         q_warray_t iq;
         warray_t a;
         warray_t b0;

         a[0] = "abcdefg_ijkl";
         a[1] = "012123123128";
         iq.push_back(a);

         b0 = iq[0];
         `checks(b0[0], "abcdefg_ijkl");
         `checks(b0[1], "012123123128");
      end
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
