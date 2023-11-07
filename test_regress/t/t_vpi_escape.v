// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2010-2023 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef USE_VPI_NOT_DPI
//We call it via $c so we can verify DPI isn't required - see bug572
`else
import "DPI-C" context function int mon_check();
`endif

module \t.has.dots (/*AUTOARG*/
   // Outputs
   \escaped_normal , double__underscore, \9num , \bra[ket]slash/dash-colon:9backslash\done , \x.y ,
   // Inputs
   clk, \b.c , a
   );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   input clk;
   input [7:0] a;
   input \b.c ;

   integer cyc; initial cyc=1;

   output  \escaped_normal ;
   wire    \escaped_normal = cyc[0];

   output  double__underscore ;
   wire  double__underscore = cyc[0];

   // C doesn't allow leading non-alpha, so must escape
   output \9num ;
   wire \9num = cyc[0];

   output  \bra[ket]slash/dash-colon:9backslash\done ;
   wire \bra[ket]slash/dash-colon:9backslash\done = cyc[0];

   output \x.y ;
   wire \x.y = cyc[0];

   wire \wire = cyc[0];

   wire \check_alias = cyc[0];
   wire \check:alias = cyc[0];
   wire \check;alias = !cyc[0];

   // These are *different entities*, bug83
   wire [31:0] \a0.cyc = ~a0.cyc;
   wire [31:0] \other.cyc = ~a0.cyc;

   integer        status;

   sub a0 (.cyc(cyc));

   sub \mod.with_dot (.cyc(cyc));

   initial begin

`ifdef VERILATOR
      status = $c32("mon_check()");
`endif
`ifdef IVERILOG
      status = $mon_check();
`endif
`ifndef USE_VPI_NOT_DPI
      status = mon_check();
`endif
      if (status != 0) begin
         $write("%%Error: C Test failed with %0d error(s)\n", status);
         $stop;
      end
      $write("%%Info: Checking results\n");
   end

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (escaped_normal != cyc[0]) $stop;
      if (\escaped_normal != cyc[0]) $stop;
      if (double__underscore != cyc[0]) $stop;
      if (\9num != cyc[0]) $stop;
      if (\bra[ket]slash/dash-colon:9backslash\done != cyc[0]) $stop;
      if (\x.y != cyc[0]) $stop;
      if (\wire != cyc[0]) $stop;
      if (\check_alias != cyc[0]) $stop;
      if (\check:alias != cyc[0]) $stop;
      if (\check;alias != !cyc[0]) $stop;
      if (\a0.cyc != ~cyc) $stop;
      if (\other.cyc != ~cyc) $stop;
      if (cyc==10) begin
         if (a != 2) $stop;
         if (\b.c != 1) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module sub (
            input [31:0] cyc
            );
   reg \b.c ;
   reg subsig1;
   reg subsig2;
`ifdef IVERILOG
   // stop icarus optimizing signals away
   wire redundant = subsig1 | subsig2 | \b.c ;
`endif
endmodule
