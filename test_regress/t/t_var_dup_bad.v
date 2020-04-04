// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  (
   /*AUTOARG*/
   // Outputs
   o, oi, og, org,
   // Inputs
   i, oi
   );

   reg    a;
   reg    a;

   integer l;
   integer l;

   bit     b;
   bit     b;

   output o;
   output o;

   input  i;
   input  i;

   output oi;
   input  oi;

   output og;
   reg    og;
   reg    og;

   output reg org;
   output reg org;

   sub0 sub0(.*);
   sub1 sub1(.*);
   sub2 sub2(.*);
   sub3 sub3(.*);
endmodule

module sub0
  (
   bad_duport,
   bad_duport
   );
   output bad_duport;
endmodule

module sub1
  (
   bad_mixport,
   output bad_mixport
   );
endmodule

module sub2
  (
   output bad_reout_port
   );
   output bad_reout_port;
endmodule

module sub3
  (output wire bad_rewire,
   output reg bad_rereg
   );
   wire bad_rewire;
   reg  bad_rereg;
endmodule
