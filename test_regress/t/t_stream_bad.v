// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Geza Lore
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [31:0] packed_data_32;
  byte         byte_in           [4];
  logic [ 3:0] x = 4'($random());

  initial begin
    packed_data_32 = {<<$random{byte_in}};
    packed_data_32 = {<<x{byte_in}};
  end

endmodule
