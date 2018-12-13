// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Chris Randall.

interface ifc;
   integer value;
   modport out_modport (output value);
endinterface

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
   } my_struct;  // verilator tag my_struct

   // This is a comment

   ifc itop();

   my_struct this_struct [2];  // verilator tag this_struct

   wire [31:0] dotted = itop.value;

endmodule
