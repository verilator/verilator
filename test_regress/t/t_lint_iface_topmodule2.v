// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2017 by Josh Redford.
// SPDX-License-Identifier: CC0-1.0

interface my_if #(
    parameter integer DW = 8
    ) ();
   logic            valid;
   logic [DW-1:0]      data;

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
      my_if.slave_mp in_if,
      my_if.master_mp out_if
   );

   assign out_if.valid = in_if.valid;
   assign out_if.data = in_if.data;

endmodule
