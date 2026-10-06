// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class C;
  rand int z, w;
  int que[$] = '{3, 4, 5};
  int arr[3] = '{5, 6, 7};
  constraint distinside {
    // BAD: dist item not integral (IEEE 1800-2017 18.5.4)
    z dist {que};
    w dist {arr};
  }
endclass

module t;
  initial begin
    C c;
    c = new;
    if (!bit'(c.randomize())) $stop;
    $finish;
  end
endmodule
