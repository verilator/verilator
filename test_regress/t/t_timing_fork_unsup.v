// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t;
  class C;
    task f;
      int x = 0;
      fork
        #6 x = 4;
        #2 x++;
        x = #4 x * 3;
      join_none
      x = 1;
    endtask
  endclass

  initial begin
    C o = new;
    o.f;
  end
endmodule
