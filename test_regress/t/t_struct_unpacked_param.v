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
  } subsubstruct_t;

  typedef struct {
    int a;
    int b;
    subsubstruct_t subsub;
    int c;
  } substruct_t;

  typedef substruct_t substruct_t_t;

  typedef struct {
    int a;
    int b;
    substruct_t_t sub;
    int c;
  } struct_t;

  // Constant value unpacked struct support is limited at the moment.
  // Only localparams are supported, returning constant unpacked structure
  // from function or passing unpacked structure as parameters is not
  // (yet) supported
  localparam struct_t MY_STRUCT = '{
      a: 10,
      b: 5,
      c: 20,
      sub: '{a: 100, b: 200, c: 150, subsub: '{default: 10}}
  };

  // Make standalone localparam to ensure MY_STRUCT is const
  localparam int C = MY_STRUCT.c;
  localparam int S_A = MY_STRUCT.sub.a;
  localparam int SS_B = MY_STRUCT.sub.subsub.b;

  initial begin
    `checkd(MY_STRUCT.a, 10);
    `checkd(MY_STRUCT.b, 5);
    `checkd(MY_STRUCT.c, 20);
    `checkd(MY_STRUCT.sub.c, 150);
    `checkd(C, 20);
    `checkd(S_A, 100);
    `checkd(SS_B, 10);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
