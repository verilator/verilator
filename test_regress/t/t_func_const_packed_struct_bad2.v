// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Todd Strader.
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef struct packed {
      logic [ 31 : 0 ] b;
      logic [ 7 : 0 ]  bar;
   } sub_params_t;

   typedef struct      packed {
      logic [ 31 : 0 ] a;
      logic [ 5 : 0 ]  foo;
      sub_params_t sub_params;
   } params_t;

   localparam P24 = f_add2(7, 8, 9);

   initial begin
      // Should never get here
      $write("*-* All Finished *-*\n");
      $finish;
   end

   function integer f_add(input params_t [ 1 : 0 ] params);
      f_add = params[0].a+params[1].sub_params.b;
      if (f_add == 15)
        $fatal(2, "f_add = 15");
   endfunction

   // Speced ok: function called from function
   function integer f_add2(input [31:0] a, input [31:0] b, input [31:0] c);
      params_t [ 1 : 0 ] params;
      sub_params_t sp0;
      sub_params_t sp1;
      sp0 = '{b:55, bar:111};
      params[0] = '{a:a, foo:11, sub_params:sp0};
      sp1 = '{b:b, bar:112};
      params[1] = '{a:12345, foo:12, sub_params:sp1};
      f_add2 = f_add(params)+c;
   endfunction
endmodule
