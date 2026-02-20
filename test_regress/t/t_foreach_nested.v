// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

typedef struct {int x[9][9];} Foo;

class Bar;
  Foo foo;

  function automatic void test();
    foreach(this.foo.x[i])
      foreach(this.foo.x[i][j])
        this.foo.x[i][j] = i * j;
    for (int i = 0; i < 9; i++)
      for (int j = 0; j < 9; j++)
        if (this.foo.x[i][j] != i * j) $stop;
  endfunction
endclass

module t;
  initial begin
    automatic Bar b = new;
    b.test;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
