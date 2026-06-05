// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t #(
    parameter bit fail = 0
) ();
  if (!(!fail)) begin
    __VnotExising__Vmodule__abc__ sentinel ();
  end
endmodule
