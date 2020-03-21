// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

package tt_pkg;
   typedef enum logic [1:0] {L0, L1, L2, L3} test_t;
endpackage

module t (/*AUTOARG*/
   // Outputs
   ob
   );

   output [1:0] ob;

   import tt_pkg::*;

   test_t a;
   test_t b;

   assign a = L0;
   assign ob = b;

   tt_buf #(.T_t(test_t))
   u_test
     (.i(a), .o(b));

endmodule

module tt_buf
  #(
    parameter type T_t = logic [0:0]
    )
   (
    input  T_t i,
    output T_t o
    );
   assign o = i;
endmodule
