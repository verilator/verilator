// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

interface inter (input logic cond, output wire a);
   parameter W;
   // Example:
   wire (weak0, weak1) [W-1:0] b = '1;
   assign (strong0, strong1) b = cond ? 'b0 : 'bz;

   assign a = b[10];

endinterface

module t (clk1, clk2);
   input wire clk1;
   input wire clk2;

   wire (weak0, weak1) a = 0;
   assign (supply0, supply1) a = 1'bz;
   assign (pull0, pull1) a = 1;

   wire [2:0] b;
   assign b = 3'b101;
   assign (supply0, supply1) b = 3'b01z;

   wire c;
   and (weak0, weak1) (c, clk1, clk2);
   assign (strong0, strong1) c = 'z;
   assign (pull0, pull1) c = 0;

   wire d;
   inter #(.W(32)) i(.cond(1'b1), .a(d));

   always begin
      if (a === 1 && b === 3'b011 && c === 0 && d === 0) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Error: a = %b, b = %b, c = %b, d = %b", a, b, c, d);
         $write("expected: a = %b, b = %b, c = %b, d = %b\n", clk1, 3'b011, 0, 0);
         $stop;
      end
   end
endmodule
