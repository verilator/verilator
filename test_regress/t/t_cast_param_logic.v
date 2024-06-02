// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t
  #(
    parameter type data_t = logic
    )
   (
    input data_t[7:0] in_data
    );

    typedef data_t[7:0] in_data_t;

    in_data_t out_data;
    always_comb out_data = in_data_t'(in_data);

endmodule
