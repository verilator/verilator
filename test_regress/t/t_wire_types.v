// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // IEEE: integer_atom_type
   wire integer w_integer;

   // IEEE: integer_atom_type
   wire logic   w_logic;

   wire logic  [1:0]    w_logic2;

   assign w_integer = -123456;

   assign w_logic = 1'b1;

   assign w_logic2 = 2'b10;

   always @ (posedge clk) begin
      `checkh(w_integer, -123456);
      `checkh(w_logic, 1'b1);
      `checkh(w_logic2, 2'b10);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
