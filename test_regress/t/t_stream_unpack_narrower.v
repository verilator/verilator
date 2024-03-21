// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Geza Lore.
// SPDX-License-Identifier: CC0-1.0

module t;

  logic [30:0] packed_data;
  logic [7:0] stream[4];

  initial begin
    packed_data = 31'h12345678;
    {>>{stream}} = packed_data;
    packed_data = {>>{stream}};
  end

endmodule
