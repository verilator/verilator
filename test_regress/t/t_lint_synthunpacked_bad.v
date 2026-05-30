// DESCRIPTION: Verilator: Test of SYNTHUNPACKED warning on unpacked port
//
// SPDX-FileCopyrightText: 2026 Lucas Amaral
// SPDX-License-Identifier: CC0-1.0

module t (input wire [7:0] data [0:3]);
  initial $display("data[0]=%h", data[0]);
endmodule
