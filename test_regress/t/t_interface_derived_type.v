// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

interface intf #(parameter type data_t = bit) ();
    data_t data;
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   sub #(.width(8)) sub8 ();
   sub #(.width(16)) sub16 ();

endmodule

module sub #(parameter int width) ();
    typedef struct packed {
        logic [0:0] [width-1:0] field;
    } user_type_t;

    intf #(.data_t(user_type_t)) the_intf ();

    logic [width-1:0] signal;

    always_comb the_intf.data.field = signal;
endmodule
