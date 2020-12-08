// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2010 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   sub sub ();

endmodule

module sub;

   wire pub /*verilator public*/;   // Ignore publics

   wire [5:0] assunu1 = 0;  // Assigned but unused

   wire [3:0] assunub2 = 0;  // Assigned but bit 2 unused

   wire [15:10] udrb2;  // [14:13,11] is undriven
   assign udrb2[15] = 0;
   assign udrb2[12] = 0;
   assign udrb2[10] = 0;

   wire       unu3;  // Totally unused

   wire [3:0] mixed;  // [3] unused & undr, [2] unused, [1] undr, [0] ok
   assign mixed[2] = 0;
   assign mixed[0] = 0;

   wire [2:0] cmdln_off;  // Suppressed by command line
   assign cmdln_off = 0;

   localparam THREE = 3;

   parameter UNUSED_P = 1;
   localparam UNUSED_LP = 2;

   genvar     unused_gv;
   genvar     ok_gv;

   initial begin
      if (0 && assunu1[0] != 0 && udrb2 != 0) begin end
      if (0 && assunub2[THREE] && assunub2[1:0]!=0) begin end
      if (0 && mixed[1:0] != 0) begin end
   end

   generate
      if (0)
        for (ok_gv = 0; ok_gv < 1; ++ok_gv) begin end
   endgenerate

endmodule
