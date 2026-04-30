// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Cls;
  const int x;
endclass

module t;
  initial begin
    const automatic Cls cls = new;
    automatic Cls cls2 = new;
    cls.x = 1;
    cls2.x = 1;

    cls = cls2;
    cls2 = cls;
  end
endmodule
