// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int unsigned v;
endclass

module t_randomize_method_with_bad();
  function automatic int unsigned in_mod_function();
    return 5;
  endfunction

  initial begin
    automatic Foo foo = new;
    automatic int res = foo.randomize() with { v < in_mod_function(); };
  end
endmodule
