// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2018 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc; initial cyc=1;

   reg [15:0] m_din;

   reg [15:0] v1;
   reg [15:0] v2;
   reg [15:0] v3;
   integer    nosplit;

   always @ (posedge clk) begin
      // write needed so that V3Dead doesn't kill v0..v3
      $write(" values %x %x %x\n", v1, v2, v3);

      // Locally-set 'nosplit' will prevent the if from splitting
      // in splitAlwaysAll(). This whole always block should still be
      // intact when we call splitReorderAll() which is the subject
      // of this test.
      nosplit = cyc;
      if (nosplit > 2) begin
         /* S1 */ v1 <= 16'h0;
         /* S2 */ v1 <= m_din;
         /* S3 */ if (m_din == 16'h0) begin
            /* X1 */ v2 <= v1;
            /* X2 */ v3 <= v2;
         end
      end

      // We expect to swap S2 and S3, and to swap X1 and X2.
      // We can check that this worked by the absense of dly vars
      // in the generated output; if the reorder fails (or is disabled)
      // we should see dly vars for v1 and v2.
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc<=cyc+1;
         if (cyc==7) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
