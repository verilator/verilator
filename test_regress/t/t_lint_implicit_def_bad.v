// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (a,z);
   input a;
   output z;

   assign imp_warn = 1'b1;
   // verilator lint_off IMPLICIT
   assign imp_ok = 1'b1;

`default_nettype none
   assign imp_err = 1'b1;

`default_nettype wire
   assign imp_ok2 = 1'b1;

`default_nettype none
`resetall
   assign imp_ok3 = 1'b1;
endmodule
