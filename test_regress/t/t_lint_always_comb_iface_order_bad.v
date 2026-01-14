// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2017 Josh Redford
// SPDX-License-Identifier: CC0-1.0

interface my_if;

   logic            valid;
   logic [7:0]      data ;

   modport slave_mp (
                     input valid,
                     input data
                     );

   modport master_mp (
                      output valid,
                      output data
                      );

endinterface

module t
  (
   input wire       in_valid,
   input wire [7:0] in_data
   );

   my_if in_i  ();
   my_if out_i ();

   assign in_i.valid   = in_valid;
   assign in_i.data    = in_data ;

   my_module my_module_i (
                          .in_i   (in_i  ),
                          .out_i  (out_i)
                          );

endmodule

module my_module (
                   my_if.slave_mp  in_i,
                   my_if.master_mp out_i
                   );

   // Gives ALWCOMBORDER warning
   always_comb
     begin
        if (out_i.valid)
          out_i.data  = in_i.data;
        else
          out_i.data  = out_i.data;
        out_i.valid = in_i.valid;
     end

endmodule
