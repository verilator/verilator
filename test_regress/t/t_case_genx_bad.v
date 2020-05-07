// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005-2007 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   parameter P = 32'b1000;

   generate
      case (P)
        32'b0:    initial begin end
        32'b1xxx: initial begin end
        default:  initial begin end
      endcase
   endgenerate

endmodule
