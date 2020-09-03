// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Josh Redford.
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
   my_if out1_i ();
   my_if out2_i ();
   my_if out3_i ();

   assign in_i.valid   = in_valid;
   assign in_i.data    = in_data ;

   my_module1 my_module1_i (
                            .in_i   (in_i  ),
                            .out_i  (out1_i)
                            );

   my_module2 my_module2_i (
                            .in_i   (in_i  ),
                            .out_i  (out2_i)
                            );

   my_module3 my_module3_i (
                            .in_i   (in_i  ),
                            .out_i  (out3_i)
                            );

endmodule

module my_module1 (
                   my_if.slave_mp  in_i,
                   my_if.master_mp out_i
                   );

   // Gives ALWCOMBORDER warning
   always_comb
     begin
        out_i.valid = in_i.valid;
        out_i.data  = in_i.data ;
     end

endmodule

module my_module2 (
                   my_if.slave_mp  in_i,
                   my_if.master_mp out_i
                   );

   // Works if you initialise to non-interface signal first
   always_comb
     begin
        out_i.valid = '0;
        out_i.data  = 'X;
        out_i.valid = in_i.valid;
        out_i.data  = in_i.data ;
     end

endmodule

module my_module3 (
                   my_if.slave_mp  in_i,
                   my_if.master_mp out_i
                   );

   // Works if you use assign signal
   assign out_i.valid  = in_i.valid;
   assign out_i.data   = in_i.data ;

endmodule
