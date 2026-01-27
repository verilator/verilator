// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface ifc;
   integer ok;
   modport out_modport (output ok);
endinterface

module t;

   ifc itop();

   counter_ansi c1 (.isub(itop),
                    .i_value(4'h4));

endmodule

module counter_ansi
  (
   ifc.oop_modport isub,  // Bad
   input logic [3:0] i_value
   );
endmodule
