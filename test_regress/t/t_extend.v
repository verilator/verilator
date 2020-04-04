// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   /*verilator public_module*/

   input clk;
   // No verilator_public needed, because it's outside the "" in the $c statement
   reg [7:0] cyc; initial cyc=0;
   reg 	  c_worked;
   reg [8:0] c_wider;

   wire      one = 1'b1;

   always @ (posedge clk) begin
      cyc <= cyc+8'd1;

      // coverage testing
      if (one) begin end
      if (!one) begin end
      if (cyc[0]) begin end   if (!cyc[0]) begin end // multiple on a line

      if (cyc == 8'd1) begin
	 c_worked <= 0;
      end
      if (cyc == 8'd2) begin
`ifdef VERILATOR
	 $c("VL_PRINTF(\"Calling $c, calling $c...\\n\");");
	 $c("VL_PRINTF(\"Cyc=%d\\n\",",cyc,");");
	 c_worked <= $c("my_function()");
	 c_wider <= $c9("0x10");
`else
	 c_worked <= 1'b1;
	 c_wider <= 9'h10;
`endif
      end
      if (cyc == 8'd3) begin
	 if (c_worked !== 1'b1) $stop;
	 if (c_wider !== 9'h10) $stop;
	 $finish;
      end
   end

`ifdef verilator
 `systemc_header
#define DID_INT_HEADER 1
 `systemc_interface
#ifndef DID_INT_HEADER
#error "`systemc_header didn't work"
#endif
   bool m_did_ctor;
   vluint32_t my_function() {
       if (!m_did_ctor) vl_fatal(__FILE__, __LINE__, __FILE__, "`systemc_ctor didn't work");
       return 1;
   }
 `systemc_imp_header
#define DID_IMP_HEADER 1
 `systemc_implementation
#ifndef DID_IMP_HEADER
#error "`systemc_imp_header didn't work"
#endif
 `systemc_ctor
   m_did_ctor = 1;
 `systemc_dtor
   printf("In systemc_dtor\n");
   printf("*-* All Finished *-*\n");
 `verilog

// Test verilator comment after a endif
`endif // verilator

endmodule
