// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit flag;
  initial begin
    fork
      begin
        $stop;
      end
    join_none
    $finish;
  end
endmodule
