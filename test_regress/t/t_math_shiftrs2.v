// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); `stop; end while(0);

module top(out35);
   output wire [2:0] out35;
   wire signed [2:0] wire_4;
   assign wire_4 = 3'b011;
   assign out35 = (wire_4 >>> 36'hffff_ffff_f);

   initial begin
      #10;
      `checkd(out35, '0);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
