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
      my_if in_if,
      my_if out_if
   );

   assign out_if.valid = in_if.valid;
   assign out_if.data = in_if.data;

   my_if my_i (.clk(clk));

   initial
   begin
       $display(in_if.DW_LOCAL);
       $display(in_if.width());
       $display(in_if.dw_ge_4_G.min_width());
       $display(out_if.DW_LOCAL);
       $display(out_if.width());
       $display(out_if.dw_ge_4_G.min_width());
   end

endmodule
