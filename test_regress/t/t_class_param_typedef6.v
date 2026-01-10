// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class pipeline_class #(
    parameter type XWORD = logic
);

  typedef struct packed {XWORD pc;} if_id_t;

endclass

module pipe_reg #(
    parameter type T = logic
) ();
  initial begin
    #1;
    `checkd($bits(T), 8);
  end
endmodule

module the_top #() ();

  typedef logic [7:0] my_t;
  typedef pipeline_class#(my_t)::if_id_t if_id2_t;
  typedef if_id2_t if_id_t;
  pipe_reg #(if_id_t) if_id_reg ();

  initial begin
    #1;
    #1;
    `checkd($bits(if_id_t), 8);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
