// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Base;
  int value;
endclass

typedef Base Base_t;

class SubA #(
    type T = int
) extends Base_t;
endclass

class SubB #(
    type T = int
) extends Base_t;
endclass

typedef SubA#(int) SubAInt_t;
typedef SubB#(int) SubBInt_t;

class Container;
  local SubAInt_t a;
  local SubBInt_t b;
  function new();
    a = new;
    a.value = 1;
    b = new;
    b.value = 2;
  endfunction
  function Base test(int sel);
    test = sel[0] ? a : b;
  endfunction
endclass

module t;
  Container c;
  int cyc;
  Base result;
  initial begin
    c = new;
    for (cyc = 0; cyc < 100; ++cyc) begin
      result = c.test(cyc);
      if (result.value != (cyc[0] ? 1 : 2)) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
