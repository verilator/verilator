// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);



module t(/*AUTOARG*/
   // Inputs
   clk
   );
   
   typedef bit bit_q_t[$];
   typedef byte byte_q_t[$];

   input clk;
   integer cyc = 0;
   logic [7:0] d;

   initial begin
      bit_q_t bit_q, bit_qq;

      bit_q.push_back(1'b0);
      bit_q.push_back(1'b1);
      bit_q.push_back(1'b1);
      `checkh(bit_q[0], 1'b0);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b1);

      bit_q = bit_q_t'(4'he);
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b0);

      bit_q = bit_q_t'(4'h3);
      bit_qq = bit_q;
      `checkh(bit_qq[0], 1'b0);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b1);

      bit_q = bit_q_t'(4'h2);
      bit_qq = bit_q_t'(bit_q);
      `checkh(bit_qq[0], 1'b0);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b0);

      bit_q = bit_q_t'({>>{4'hd}});
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b0);
      `checkh(bit_q[3], 1'b1);

      bit_q = bit_q_t'({<<{4'hc}});
      `checkh(bit_q[0], 1'b0);
      `checkh(bit_q[1], 1'b0);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b1);

      bit_q = {>>{bit_q_t'(4'he)}};
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b0);

      bit_q = {<<{bit_q_t'(4'hd)}};
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b0);
      `checkh(bit_q[2], 1'b1);
      `checkh(bit_q[3], 1'b1);

      bit_qq = {>>{bit_q}};
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b0);
      `checkh(bit_qq[2], 1'b1);
      `checkh(bit_qq[3], 1'b1);

      bit_qq = {<<{bit_q}};
      `checkh(bit_qq[0], 1'b1);
      `checkh(bit_qq[1], 1'b1);
      `checkh(bit_qq[2], 1'b0);
      `checkh(bit_qq[3], 1'b1);

      bit_q = bit_q_t'({>>{4'hd}});
      `checkh(bit_q[0], 1'b1);
      `checkh(bit_q[1], 1'b1);
      `checkh(bit_q[2], 1'b0);
      `checkh(bit_q[3], 1'b1);
      
      // TODO: fix. This results in:
      //     VL_REVCOPY_Q(t__DOT__unnamedblk1__DOT__bit_qq, VL_CLONE_Q
      //           (VL_STREAML_FAST_III(0, vlSelfRef.t__DOT__unnamedblk1__DOT__bit_q, 0)));
      // Which is problematic because VL_CLONE_Q expects a VlQueue but
      // VL_STREAML_FAST_III produces an IData in this case. To fix this
      // requires further digging in V3Width/V3Const for that inner streamL
      // and/or cast operation.
      //
      // bit_qq = {<<2{bit_q_t'({<<{bit_q}})}};
      // `checkh(bit_qq[0], 1'b1);
      // `checkh(bit_qq[1], 1'b1);
      // `checkh(bit_qq[2], 1'b1);
      // `checkh(bit_qq[3], 1'b0);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
