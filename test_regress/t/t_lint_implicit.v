// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Wilson Snyder.

module t (a,z);
   input a;
   output z;

   assign b = 1'b1;

   or   OR0 (nt0, a, b);

   logic [1:0] dummy_ip;
   assign {dummy1, dummy2} = dummy_ip;

   assign z = nt0;
endmodule
