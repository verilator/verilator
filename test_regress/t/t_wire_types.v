// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

   // IEEE: integer_atom_type
   wire byte    w_byte;
   wire shortint w_shortint;
   wire int     w_int;
   wire longint w_longint;
   wire integer w_integer;

   // IEEE: integer_atom_type
   wire bit     w_bit;
   wire logic   w_logic;

   wire bit [1:0]       w_bit2;
   wire logic  [1:0]    w_logic2;

   // IEEE: non_integer_type
   //UNSUP shortreal    w_shortreal;
   wire real            w_real;

   assign w_byte = 8'h12;
   assign w_shortint = 16'h1234;
   assign w_int = -123456;
   assign w_longint = -1234567;
   assign w_integer = -123456;

   assign w_bit = 1'b1;
   assign w_logic = 1'b1;

   assign w_bit2 = 2'b10;
   assign w_logic2 = 2'b10;

   assign w_real = 3.14;

   always @ (posedge clk) begin
      `checkh(w_byte, 8'h12);
      `checkh(w_shortint, 16'h1234);
      `checkh(w_int, -123456);
      `checkh(w_longint, -1234567);
      `checkh(w_integer, -123456);
      `checkh(w_bit, 1'b1);
      `checkh(w_logic, 1'b1);
      `checkh(w_bit2, 2'b10);
      `checkh(w_logic2, 2'b10);
      `checkr(w_real, 3.14);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
