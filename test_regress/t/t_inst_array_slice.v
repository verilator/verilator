// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  localparam int unsigned LARGE_ARRAY[5] = '{1, 2, 3, 4, 5};
  localparam int unsigned SMALL_ARRAY[2] = LARGE_ARRAY[1+:2];
  sub #(.VAL(SMALL_ARRAY)) u_sub ();
endmodule

module sub #(
    parameter int unsigned VAL[2] = '{1, 2}
) ();
  initial begin
    `checkd(VAL[0], 2);
    `checkd(VAL[1], 3);
    $finish;
  end
endmodule
