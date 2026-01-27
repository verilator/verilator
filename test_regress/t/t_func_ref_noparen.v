// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class c;
  function bit f();
    return 1'b0;
  endfunction
endclass
module t;
  c cinst;
  initial begin
    cinst = new();
    if (cinst.f) begin
    end
  end
endmodule
