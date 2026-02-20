// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Cls;
   Cls f;
   rand int r;
endclass
module t;
   Cls x = new;
   int i;
   initial $display(
      x.f.randomize(),
      x.f.randomize() with { r < 5; },
      i.randomize() with { v < 5; });
endmodule
