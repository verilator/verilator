// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module a;
   c c ();
   initial begin
      $write("Bad top modules\n");
      $stop;
   end
endmodule

module a2;
   initial begin
      $write("Bad top modules\n");
      $stop;
   end
endmodule

module b;
   d d ();
endmodule

module c;
   initial begin
      $write("Bad mid modules\n");
      $stop;
   end
endmodule

module d;
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
