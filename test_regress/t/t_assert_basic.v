// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg   toggle;

   integer cyc; initial cyc=1;
   wire [7:0] cyc_copy = cyc[7:0];

   always @ (negedge clk) begin
      AssertionFalse1: assert (cyc<100);
      assert (!(cyc==5) || toggle);
      // FIX cover  {cyc==3 || cyc==4};
      // FIX cover {cyc==9} report "DefaultClock,expect=1";
      // FIX cover  {(cyc==5)->toggle} report "ToggleLogIf,expect=1";
   end

   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         toggle <= !cyc[0];
         if (cyc==7) assert (cyc[0] == cyc[1]);  // bug743
         if (cyc==9) begin
`ifdef FAILING_ASSERTIONS
            assert (0) else $info;
            assert (0) else $info("Info message");
            assume (0) else $info("Info message from failing assumption");
            assert (0) else $info("Info message, cyc=%d", cyc);
            InWarningBlock: assert (0) else $warning("Warning.... 1.0=%f 2.0=%f", 1.0, 2.0);
            InErrorBlock: assert (0) else $error("Error....");
            assert (0) else $fatal(1,"Fatal....");
`endif
         end
         if (cyc==10) begin
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end

endmodule
