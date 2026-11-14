// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  logic tick;
  bit flag;
  // 'tick' is only in an event control, so the implicit event list is empty
  always @* begin
    @(posedge tick);
    flag = 1'b1;
  end
endmodule
