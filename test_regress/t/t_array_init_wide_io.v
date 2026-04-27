// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test for issue #6904: Large array initialization with wide elements
// for I/O ports generates invalid C++ code.

module t (/*AUTOARG*/
   // Outputs
   output_wide, output_nonwide,
   // Inputs
   clk
   );

   input clk;

   // Wide (>64 bits) output port with >256 elements - the original bug
   output logic [64:0] output_wide [257];
   assign output_wide = '{default: '0};

   // Non-wide output port with >256 elements - should still use optimization
   output logic output_nonwide [257];
   assign output_nonwide = '{default: '0};

   // Wide internal variable with >256 elements - uses VlUnpacked
   logic [64:0] internal_wide [257];
   initial internal_wide = '{default: '0};

   integer cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         // Verify initialization worked
         if (output_wide[0] !== 65'b0) $stop;
         if (output_wide[256] !== 65'b0) $stop;
         if (output_nonwide[0] !== 1'b0) $stop;
         if (output_nonwide[256] !== 1'b0) $stop;
         if (internal_wide[0] !== 65'b0) $stop;
         if (internal_wide[256] !== 65'b0) $stop;
         $write("*-* All Coverage Met *-*\n");
         $finish;
      end
   end

endmodule
