// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   reg [40:0] disp; initial disp = 41'ha_bbbb_cccc;
   initial begin
      // Display formatting
      $display("%x");  // Too few
      $display("%x",disp,disp);  // Too many
      $display("%q");  // Bad escape
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
