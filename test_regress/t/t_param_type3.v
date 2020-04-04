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

   sub #(.T_t(T_t))
   sub (.i, .o);

   sub2 #(.T_t(T_t))
   sub2 (.i, .o(o2));

endmodule

module sub (i,o);
   parameter type T_t = logic;
   localparam type T2_t = T_t;
   input  T_t i;
   output T2_t o;
   assign o = i;
endmodule

module sub2
  #(
    parameter type T_t = logic,
    localparam type T2_t = T_t
    )
   (
    input  T_t i,
    output T_t o
    );
   assign o = i;
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
