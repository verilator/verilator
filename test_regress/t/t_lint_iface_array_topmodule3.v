// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Josh Redford.
// SPDX-License-Identifier: CC0-1.0

interface my_if #( parameter integer DW = 8 ) (input clk);

   localparam DW_LOCAL = DW;

   logic            valid;
   logic [DW-1:0]   data;

   modport slave_mp (
                     input valid,
                     input data
                     );

   modport master_mp (
                      output valid,
                      output data
                      );

   function automatic integer width();
       return $bits(data);
   endfunction

   generate
       if (DW < 4)
       begin: dw_lt_4_G
           function automatic integer min_width();
               return 4;
           endfunction
       end
       else
       begin: dw_ge_4_G
           function automatic integer min_width();
               return 8;
           endfunction
       end
   endgenerate

endinterface

module t
  (
      input wire clk,
      my_if in_if [2],
      my_if out_if [2]
   );

   assign out_if[0].valid = in_if[0].valid;
   assign out_if[0].data = in_if[0].data;

   assign out_if[1].valid = in_if[1].valid;
   assign out_if[1].data = in_if[1].data;

   my_if my_i (.clk(clk));

   initial
   begin
       $display(in_if[0].DW_LOCAL);
       $display(in_if[0].width());
       $display(in_if[0].dw_ge_4_G.min_width());
       $display(out_if[0].DW_LOCAL);
       $display(out_if[0].width());
       $display(out_if[0].dw_ge_4_G.min_width());

       $display(in_if[1].DW_LOCAL);
       $display(in_if[1].width());
       $display(in_if[1].dw_ge_4_G.min_width());
       $display(out_if[1].DW_LOCAL);
       $display(out_if[1].width());
       $display(out_if[1].dw_ge_4_G.min_width());
   end

endmodule
