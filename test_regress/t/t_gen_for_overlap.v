// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Wilson Snyder.

// bug749

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   genvar g;
   for (g=1; g<3; ++g) begin : gblk
      sub2 #(.IN(g)) u ();
      //sub #(.IN(g)) u2 ();
   end

   sub1 #(.IN(0)) u ();

   always @ (posedge clk) begin
      if (t.u.IN != 0) $stop;
      if (t.u.FLAVOR != 1) $stop;
      //if (t.u2.IN != 0) $stop;  // This should be not found
      if (t.gblk[1].u.IN != 1) $stop;
      if (t.gblk[2].u.IN != 2) $stop;
      if (t.gblk[1].u.FLAVOR != 2) $stop;
      if (t.gblk[2].u.FLAVOR != 2) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

module sub1 (/*AUTOARG*/);
   parameter [31:0] IN = 99;
   parameter FLAVOR = 1;
`ifdef TEST_VERBOSE
   initial $display("%m");
`endif
endmodule

module sub2 (/*AUTOARG*/);
   parameter [31:0] IN = 99;
   parameter FLAVOR = 2;
`ifdef TEST_VERBOSE
   initial $display("%m");
`endif
endmodule
