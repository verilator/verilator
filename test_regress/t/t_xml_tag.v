// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Chris Randall.

module m
  (
   input  clk_ip, //  verilator tag clk_ip
   input  rst_ip,
   output foo_op);  // verilator tag foo_op

   // This is a comment

   typedef struct packed  {
      logic 	  clk;    /* verilator tag this is clk */
      logic 	  k;      /* verilator lint_off UNUSED */
      logic 	  enable; // verilator tag enable
      logic 	  data;   // verilator tag data
   } my_struct;

   // This is a comment

   my_struct this_struct [2];

endmodule
