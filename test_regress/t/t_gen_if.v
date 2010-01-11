// DESCRIPTION: Verilator: Verilog Test module
//   simplistic example, should choose 1st conditional generate and assign straight through
//   the tool also compiles the special case and determines an error (replication value is 0)
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty.
`timescale 1ns / 1ps

module t(data_i, data_o, single);
   parameter op_bits = 32;
   input [op_bits -1:0] data_i;
   output [31:0] data_o;
   input single;

   //simplistic example, should choose 1st conditional generate and assign straight through
   //the tool also compiles the special case and determines an error (replication value is 0
   generate
      if (op_bits == 32) begin : general_case
         assign data_o = data_i;
	 // Test implicit signals
	 /* verilator lint_off IMPLICIT */
	 assign imp = single;
	 /* verilator lint_on IMPLICIT */
         end
      else begin : special_case
         assign data_o = {{(32 -op_bits){1'b0}},data_i};
	 /* verilator lint_off IMPLICIT */
	 assign imp = single;
	 /* verilator lint_on IMPLICIT */
         end
   endgenerate
endmodule
