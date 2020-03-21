// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package p3;
   typedef enum logic [2:0] {
          ZERO = 3'b0,
          ONE = 3'b1 } e3_t /*verilator public*/;
endpackage

package p62;
   typedef enum logic [62:0] {
          ZERO = '0,
          ALLONE = '1 } e62_t /*verilator public*/;
endpackage

module t (/*AUTOARG*/);

   enum integer {
		 EI_A,
		 EI_B,
		 EI_C
		 } m_state;

   initial begin
      m_state = EI_A;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
