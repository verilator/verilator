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
      input wire clk,
      my_if.slave_mp in_if [2],
      my_if.master_mp out_if [2]
   );

   my_if my_i [2] ();

   always @(posedge clk)
   begin
       my_i[0].valid <= in_if[0].valid;
       my_i[0].data <= in_if[0].data;

       my_i[1].valid <= in_if[1].valid;
       my_i[1].data <= in_if[1].data;
   end

   assign out_if[0].valid = my_i[0].valid;
   assign out_if[0].data = my_i[0].data;

   assign out_if[1].valid = my_i[1].valid;
   assign out_if[1].data = my_i[1].data;

endmodule
