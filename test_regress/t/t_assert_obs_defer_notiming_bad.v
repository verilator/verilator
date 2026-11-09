// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    assert #0 (0)
    else $display("fail");
    assert #0 (0);
    assert #0 (0) $display("pass");
    else $display("fail");
    cover #0 (0);
  end
endmodule
