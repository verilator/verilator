// DESCRIPTION: Verilator: Verilog Test module
//
// This files is used to generated the following error:
// %Error: Internal Error: t/t_unroll_forfor.v:27: ../V3Simulate.h:177: No value found for node.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Jan Egil Ruud.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk, in
   );
   input clk;
   input [71:0] in;

   reg [71:0] in_tmp;

   localparam [71:0] TEST_PARAM = {72{1'b0}};

   // Test loop
   always @*
     begin: testmap
	byte i, j;
	// bug1044
	for ( i = 0; i < 9; i = i + 1 )
          for ( j=0; j<(TEST_PARAM[i*8+:8]); j=j+1 )
            begin
	       // verilator lint_off WIDTH
               in_tmp[TEST_PARAM[i*8+:8]+j] = in[TEST_PARAM[i*8+:8]+j];
	       // verilator lint_on WIDTH
            end
	$write("*-* All Finished *-*\n");
	$finish;
     end
endmodule
