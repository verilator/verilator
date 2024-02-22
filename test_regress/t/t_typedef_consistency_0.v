// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   typedef logic l;
endpackage

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire logic  o_logic;
   // Using 'pkg::l' instead of 'logic' should make no difference
   wire pkg::l o_alias;

   sub sub_logic(o_logic);
   sub sub_alias(o_alias);

   assign o_logic = clk;
   assign o_alias = clk;

   always @(posedge clk) begin
     $display("o_logic: %b o_alias: %b", o_logic, o_alias);
     // Whatever the answer is, it should be the same
     if (o_logic !== o_alias) $stop;
     $write("*-* All Finished *-*\n");
     $finish;
   end

endmodule

module sub(output wire  o);
endmodule
