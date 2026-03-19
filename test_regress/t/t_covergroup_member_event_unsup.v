// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t(input clk);
  class Packet;
    int m_z;
    int m_x;
    covergroup cov1 @m_z;
      coverpoint m_x;
    endgroup
  endclass
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
