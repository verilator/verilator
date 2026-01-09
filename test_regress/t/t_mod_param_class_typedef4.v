// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class p_class #(
    parameter TLEN = 2,
    localparam type T = logic [TLEN-1:0]
);
  typedef struct packed {T a, b;} p_type;
endclass

module p_mod #(
    parameter type T = logic
);
  initial begin
    #1;
    `checkd($bits(T), 16);
  end
endmodule

module the_top #() ();
  p_mod #(.T(p_class#(8)::p_type)) p1 ();

  typedef p_class#(8) p_class_8;
  p_mod #(.T(p_class_8::p_type)) p2 ();

  typedef p_class_8::p_type p_type_8;
  p_mod #(.T(p_type_8)) p3 ();

  typedef p_class#(8)::p_type p_class_type_8;
  p_mod #(.T(p_class_type_8)) p4 ();

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
