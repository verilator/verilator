// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

interface intf #(
    parameter type data_t = bit,
    parameter int arr[2][4]
) ();
    data_t data;
    // TODO -- some kind of issue with multi-dimensional array constness:
    // %Error: t/t_interface_derived_type.v:12:12: Expecting expression to be constant, but variable isn't const: 'arr'
    //                                           : ... note: In instance 't.sub16'
    //    19 |     logic [arr[0][0]-1:0] other_data;
    //       |            ^~~
    // `define SHOW_2D_BUG
    `ifdef SHOW_2D_BUG
    logic [arr[0][0]-1:0] other_data;
    `else
    logic [$bits(data)-1:0] other_data;
    `endif
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

   sub #(.width(8), .arr('{'{8, 2, 3, 4}, '{1, 2, 3, 4}})) sub8 ();
   sub #(.width(16), .arr('{'{16, 2, 3, 4}, '{1, 2, 3, 4}})) sub16 ();

endmodule

module sub #(
    parameter int width,
    parameter int arr[2][4]
) ();
    typedef struct packed {
        logic [3:3] [0:0] [width-1:0] field;
    } user_type_t;

    intf #(
        .data_t(user_type_t),
        .arr(arr)
    ) the_intf ();

    logic [width-1:0] signal;

    always_comb begin
        the_intf.data.field = signal;
        the_intf.other_data = signal;
    end
endmodule
