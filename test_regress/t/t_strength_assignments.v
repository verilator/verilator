// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   wire a;
   assign (weak0, weak1) a = 1;
   assign (weak0, supply1) a = 1;
   assign (strong0, strong1) a = 0;

   wire (weak0, weak1) b = 1;
   assign (strong0, strong1) b = 0;

   wire [1:0] c;
   assign (weak0, supply1) c = '1;
   assign (supply0, pull1) c = '1;
   assign (strong0, strong1) c = '0;

   supply0 d;
   assign (strong0, strong1) d = 1;

   wire (supply0, supply1) e = 'z;
   assign (weak0, weak1) e = 1;

   always begin
      if (a && !b && c === '1 && !d && e) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: a = %b, b = %b, c = %b, d = %b, e = %b ", a, b, c, d, e);
         $write("expected: a = 1, b = 0, c = 11, d = 0, e = 1\n");
         $stop;
      end
   end
endmodule
