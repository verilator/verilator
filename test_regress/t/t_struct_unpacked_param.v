// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Jonathan Drolet.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  typedef struct {
    int a;
    int b;
    int c;
  } struct_t;

  // Constant value unpacked struct support is limited at the moment.
  // Only localparams are supported, returning constant unpacked structure
  // from function or passing unpacked structure as parameters is not
  // (yet) supported
  localparam struct_t MY_STRUCT = '{a: 10, b: 5, c: 20};

  // Make standalone localparam to ensure MY_STRUCT is const
  localparam int C = MY_STRUCT.c;

  initial begin
    `checkd(MY_STRUCT.a, 10);
    `checkd(MY_STRUCT.b, 5);
    `checkd(MY_STRUCT.c, 20);
    `checkd(C, 20);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
