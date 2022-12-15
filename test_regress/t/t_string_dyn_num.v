// DESCRIPTION: Verilator: Verilog Test module
//
// Use this file as a template for submitting bugs, etc.
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// The code as shown applies a random vector to the Test
// module, then calculates a CRC on the Test module's outputs.
//
// **If you do not wish for your code to be released to the public
// please note it here, otherwise:**
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   reg [31:0] istr;
   string     sstr;
   string     v;

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d istr='%s' sstr='%s'\n", $time, cyc, istr, sstr);
`endif
      cyc <= cyc + 1;
      sstr <= string'(istr);  // Note takes another cycle
      if (cyc < 10) begin
         istr <= 32'h00_00_00_00;
      end
      else if (cyc == 13) begin
         // These displays are needed to check padding of %s
         $display("istr='%s' istr%%0='%0s' sstr='%s'", istr, istr, sstr);
         if (sstr.len() != 0) $stop;
         if (sstr != "") $stop;
      end
      else if (cyc == 20) begin
         istr <= 32'h00_00_41_00;
      end
      else if (cyc == 23) begin
         $display("istr='%s' istr%%0='%0s' sstr='%s'", istr, istr, sstr);
         if (sstr.len() != 1) $stop;
         if (sstr != "A") $stop;
      end
      else if (cyc == 30) begin
         istr <= 32'h42_00_41_00;
      end
      else if (cyc == 33) begin
         $display("istr='%s' istr%%0='%0s' sstr='%s'", istr, istr, sstr);
         if (sstr.len() != 2) $stop;
         if (sstr != "BA") $stop;
      end
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
