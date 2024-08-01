// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2004 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   // verilator_no_inline_module
   initial begin
      case (1'b1) // synopsys_full_case
      endcase
      $stop; // Should have failed
   end

endmodule
