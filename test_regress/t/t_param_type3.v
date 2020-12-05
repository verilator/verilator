// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

typedef logic T_t;

module t (/*AUTOARG*/
   // Outputs
   o, o2,
   // Inputs
   i
   );

   input T_t i;
   output T_t o;
   output T_t o2;

   sub1 #(.T_t(T_t), .CHECK(1))
   sub1 (.i, .o);

   sub2 #(.T_t(T_t), .CHECK(2))
   sub2 (.i, .o(o2));

   sub1 #(T_t, 1)
   sub1b (i, o);

   sub2 #(T_t, 2)
   sub2b (i, o2);

endmodule

module sub1 (i,o);
   parameter type T_t = real;
   localparam type T2_t = T_t;
   parameter int CHECK = 0;
   input  T_t i;
   output T2_t o;
   assign o = i;
   if (CHECK != 1) $error;
endmodule

module sub2
  #(
    parameter type T_t = real,
    localparam type T2_t = T_t,
    parameter int CHECK = 0
    )
   (
    input  T_t i,
    output T_t o
    );
   assign o = i;
   if (CHECK != 2) $error;
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
