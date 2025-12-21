// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

class p_class #(
    parameter TLEN = 2,
    localparam type T = logic [TLEN-1:0]
);
  typedef struct packed {T a;} p_type;
endclass

module p_mod #(
    parameter type T = logic
);
  initial begin
    #1;
    `checkd($bits(T), 8);
  end
endmodule

module the_top #() ();
  typedef p_class#(8)::p_type p_type_t;
  p_mod #(p_type_t) p1 ();

  p_mod #(p_class#(8)::p_type) p2 ();

  initial begin
    #2;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
