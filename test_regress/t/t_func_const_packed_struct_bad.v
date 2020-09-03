// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef struct packed {
      logic [ 31 : 0 ] a;
      logic [ 31 : 0 ] b;
   } params_t;

   localparam P24 = f_add2(7, 8, 9);

   initial begin
      // Should never get here
      $write("*-* All Finished *-*\n");
      $finish;
   end

   function integer f_add(input params_t [ 1 : 0 ] params);
      f_add = params[0].a+params[1].b;
      if (f_add == 15)
        $fatal(2, "f_add = 15");
   endfunction

   // Speced ok: function called from function
   function integer f_add2(input [31:0] a, input [31:0] b, input [31:0] c);
      params_t [ 1 : 0 ] params;
      params[0] = '{a:a, b:555};
      params[1] = '{a:12345, b:b};
      f_add2 = f_add(params)+c;
   endfunction
endmodule
