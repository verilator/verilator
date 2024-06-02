// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

    function integer max2;
       input integer x;
       input integer y;
       begin
          begin : blk
             automatic int temp;
             temp = x;
          end
       end
       max2 = ( x > y ) ? x : y;
    endfunction

    function integer max4;
       input integer x;
       input integer y;
       input integer z;
       input integer w;
       // MAX2 is used multiple times
       max4 = max2( max2( x, y ), max2( z, w ) );
    endfunction

   localparam  MAX4 = max4( 1, 1, 0, 0 );

   initial begin
      if (MAX4 != 1) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
