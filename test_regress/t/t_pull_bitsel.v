// DESCRIPTION: Verilator: Test pullup/pulldown with bit-select assigns
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Lucas Amaral.
// SPDX-License-Identifier: CC0-1.0

// Bug: When a module has bit-select assigns (e.g., out[17:0] = in[17:0])
// combined with pullup/pulldown tie cells for other bits, the enable
// for the assigns incorrectly covers all bits, causing the pull constant
// to be optimized away.

// verilator lint_off PINMISSING

// Tie cell with pullup/pulldown (like sky130_fd_sc_hd__conb)
module conb(output HI, output LO);
   pullup   pu (HI);
   pulldown pd (LO);
endmodule

// Wrapper that instantiates tie cell and connects to specific bit
module tiecell_1(output HI, output LO);
   conb base (.HI(HI), .LO(LO));
endmodule

// Module similar to Mask: passthrough for some bits, tie cells for others
module top(input [31:0] in_value, output [31:0] out_value);
   // Passthrough for bits 0-7 (element 0)
   assign out_value[7:0] = in_value[7:0];

   // Bits 8-15 (element 1): bit 15 = pullup, rest = pulldown
   tiecell_1 u_hi (.HI(out_value[15]));
   tiecell_1 u_lo_8 (.LO(out_value[8]));
   tiecell_1 u_lo_9 (.LO(out_value[9]));
   tiecell_1 u_lo_10 (.LO(out_value[10]));
   tiecell_1 u_lo_11 (.LO(out_value[11]));
   tiecell_1 u_lo_12 (.LO(out_value[12]));
   tiecell_1 u_lo_13 (.LO(out_value[13]));
   tiecell_1 u_lo_14 (.LO(out_value[14]));

   // Passthrough for bits 16-31
   assign out_value[31:16] = in_value[31:16];
endmodule

module t(/*AUTOARG*/);

   // Use wire with assign - values propagate in same delta cycle
   wire [31:0] in_value = 32'hDEAD_0000;
   wire [31:0] out_value;

   top dut (.in_value(in_value), .out_value(out_value));

   // Expected: bits 31:16 = DEAD (passthrough), bit 15 = 1 (pullup),
   //           bits 14:8 = 0 (pulldown), bits 7:0 = 00 (passthrough)
   wire [31:0] expected = 32'hDEAD_8000;

   initial begin
      // Check after settle - use $display first to show values
      $display("in_value = %h, out_value = %h, expected = %h", in_value, out_value, expected);

      if (out_value !== expected) begin
         $display("%%Error: out_value = %h, expected %h", out_value, expected);
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
