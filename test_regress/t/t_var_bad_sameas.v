// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   integer varfirst;
   sub varfirst ();  // Error: Cell hits var
   task varfirst; begin end endtask  // Error: Task hits var

   sub cellfirst ();
   integer cellfirst;  // Error: Var hits cell
   task cellfirst; begin end endtask  // Error: Task hits cell

   task taskfirst; begin end endtask
   integer taskfirst;  // Error: Var hits task
   sub taskfirst ();  // Error: Cell hits task

endmodule

module sub;
endmodule
