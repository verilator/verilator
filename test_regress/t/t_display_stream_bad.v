// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  int value = 1;

  initial begin
    $display({<<{value}});
    $display("%0d", {<<{value}});
    void'($sformatf("%0d", {<<{value}}));
  end
endmodule
