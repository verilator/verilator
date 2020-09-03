// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Ian Thompson.
// SPDX-License-Identifier: CC0-1.0

//bug1099

typedef struct packed {
   logic       foo;
} some_struct_t;

module child ();
   logic a_bad;
   // bar is in the parent module, but illegal to reference without module name
   assign a_bad = bar.foo;
endmodule

module parent
  #(
    parameter PARAM = 0
    )
   (
    );
   some_struct_t bar;
   child c ();
endmodule

module t ();
   // The parameter must be anything other than the default
   parent #( 1 ) p ();
endmodule
