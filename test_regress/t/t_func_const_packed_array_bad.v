// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module t;

   localparam [ 1 : 0 ] [ 31 : 0 ] P = {32'd5, 32'd1};
   localparam P6 = f_add(P);
   localparam P14 = f_add2(2, 3, f_add(P));
   localparam P24 = f_add2(7, 8, 9);

   initial begin
      // Should never get here
      $write("*-* All Finished *-*\n");
      $finish;
   end

   function integer f_add(input [ 1 : 0 ] [ 31 : 0 ] params);
      f_add = params[0]+params[1];
      if (f_add == 15)
        $fatal(2, "f_add = 15");
   endfunction

   // Speced ok: function called from function
   function integer f_add2(input [31:0] a, input [31:0] b, input [31:0] c);
      logic [ 1 : 0 ] [ 31 : 0 ] params;
      params[0] = a;
      params[1] = b;
      f_add2 = f_add(params)+c;
   endfunction
endmodule
