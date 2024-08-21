// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand int unsigned v;
endclass

module t_randomize_method_with_bad();
  function automatic int unsigned in_mod_function();
    return 5;
  endfunction

  initial begin
    Foo foo = new;
    int res = foo.randomize() with { v < in_mod_function(); };
  end
endmodule
