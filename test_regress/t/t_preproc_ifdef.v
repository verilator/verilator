// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);
   integer num;
   initial begin
      num = 0;

`define EMPTY_TRUE
`ifndef EMPTY_TRUE
  `error "Empty is still true"
`endif

`define A
`ifdef A	$display("1A"); num = num + 1;
 `ifdef C	$stop;
 `elsif A	$display("2A"); num = num + 1;
  `ifdef C	$stop;
  `elsif B	$stop;
  `else		$display("3A"); num = num + 1;
  `endif
 `else		$stop;
 `endif
 `elsif B	$stop;
  `ifdef A	$stop;
  `elsif A	$stop;
  `else
  `endif
`elsif C	$stop;
`else		$stop;
`endif
      if (num == 3) begin
	 $write("*-* All Finished *-*\n");
	 $finish;
      end
      else begin
	 $write("%%Error: Bad count: %d\n", num);
	 $stop;
      end
   end
endmodule
