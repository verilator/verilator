// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Class_A #(
    parameter int myparam = 32
);
endclass

module tb_top;
  localparam int WIDTH_A = 32;
  localparam int WIDTH_B = 2 * 16;

  Class_A #(32) a;
  Class_A #(WIDTH_A) b;
  Class_A #(WIDTH_B) c;

  initial begin
    #1;

    a = b;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
