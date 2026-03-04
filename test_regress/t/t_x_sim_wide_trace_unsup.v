// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [100:0] x;
  initial begin
    $dumpfile("file.vcd");
    $dumpvars();
  end
endmodule
