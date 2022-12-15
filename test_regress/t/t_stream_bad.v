// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t;

   logic [31:0] packed_data_32;
   byte          byte_in[4];

   initial packed_data_32 = {<<$random{byte_in}};

endmodule
