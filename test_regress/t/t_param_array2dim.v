// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Dustin Richmond
// SPDX-License-Identifier: CC0-1.0

// Test: 2D array parameter passed to sub-modules via generate loops

module baz
  #(
    parameter integer type_p = '0
    )
   ();

endmodule

module t
  #(
    parameter integer n_x_p = 4
    ,parameter integer n_y_p = 4
    ,parameter integer twodim_p [0:n_y_p-1][0:n_x_p-1] = '{n_y_p{'{n_x_p{0}}}}
    )
   ();

   genvar r, c;

   for (r = 0; r < n_y_p; r = r+1)
     begin: y
        for (c = 0; c < n_x_p; c=c+1)
          begin: x
        baz
            #(.type_p(twodim_p[r][c]))
        baz_i
            ();
          end
     end

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
