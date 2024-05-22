// DESCRIPTION: Verilator: Verilog Test module
//
// This module takes a single clock input, and should either
//      $write("*-* All Finished *-*\n");
//      $finish;
// on success, or $stop.
//
// issue #5125
// type used for __Vtrigprevexpr signal do not match type used for i/o port
//
// Generated C++ code should compile.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Pawel Jewstafjew (Pawel.Jewstafjew@gmail.com).
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;

   logic a;
   logic d;

   top i_top(.*);

   integer cnt;
   initial cnt=1;

   always @ (posedge clk)
   begin
      cnt <= cnt + 1;

      a <= cnt[0];
      $display("%d %d %d", cnt, a, d);
      if (d != a)
	 $stop;

      if (cnt == 10) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
   end

endmodule


module top (
input  a,
output d
);

logic b;
logic  c[1];
assign c[0] = b;

unit i_unit
(
.a (a),
.b (b),
.c (c),
.d (d)
);

endmodule


module unit
(
input a,
input c[1],
output logic b,
output logic d
);

// no_inline required to prevent optimising away the interesing part ...
/*verilator no_inline_module*/

always_comb
begin
  b = a;
  d = b && c[0];
end

endmodule
