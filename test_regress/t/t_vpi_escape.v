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
  \escaped_normal , double__underscore, double__underscore__vlt, \9num ,
  \bra[ket]slash/dash-colon:9backslash\done , \x.y ,
  // Inputs
  clk, a, \b.c
  );

`ifdef VERILATOR
`systemc_header
extern "C" int mon_check();
`verilog
`endif

   input clk;
   input [7:0] a /*verilator public_flat_rw*/;
   input \b.c  /*verilator public_flat_rw*/;

   int cyc /*verilator public_flat_rd*/;

   output  \escaped_normal /*verilator public_flat_rd*/;
   wire    \escaped_normal = cyc[0];

   output  double__underscore /*verilator public_flat_rd*/;
   wire  double__underscore = cyc[0];
   output  double__underscore__vlt;   // public in .vlt
   wire  double__underscore__vlt = cyc[0];

   // C doesn't allow leading non-alpha, so must escape
   output \9num ;
   wire \9num = cyc[0];

   output  \bra[ket]slash/dash-colon:9backslash\done ;
   wire \bra[ket]slash/dash-colon:9backslash\done = cyc[0];

   output \x.y /*verilator public_flat_rd*/;
   wire \x.y = cyc[0];

   wire \wire = cyc[0];

   wire \check_alias /*verilator public_flat_rd*/ = cyc[0];
   wire \check:alias /*verilator public_flat_rd*/ = cyc[0];
   wire \check;alias /*verilator public_flat_rd*/ = !cyc[0];

   // These are *different entities*, bug83
   wire [31:0] \a0.cyc = ~a0.cyc;
   wire [31:0] \other.cyc = ~a0.cyc;

   integer        status;

   sub_with_very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very_long_name a0 (.cyc(cyc));

   sub_with_very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very_long_name \mod.with_dot (.cyc(cyc));

   // Check if scope names are not decoded twice
   sub_with_very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very_long_name ___0F_ (.cyc(cyc));
   sub_with_very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very_long_name ___0_ (.cyc(cyc));

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

module sub_with_very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very__very_long_name (
            input [31:0] cyc /*verilator public_flat_rd*/
            );
   reg \b.c /*verilator public_flat_rw*/;
   reg subsig1 /*verilator public_flat_rd*/;
   reg subsig2; // public in .vlt
`ifdef IVERILOG
   // stop icarus optimizing signals away
   wire redundant = subsig1 | subsig2 | \b.c ;
`endif
endmodule
