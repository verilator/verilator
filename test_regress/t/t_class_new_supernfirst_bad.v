// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class base_reg_block;
  function new(string name, int x);
    if (name == x) $finish;
  endfunction

  function string build_coverage(int x);
    return $sformatf("%0d", x);
  endfunction
endclass

class spi_reg_block extends base_reg_block;
  function new();
    int x = $random();
    super.new(build_coverage(x), x);  // <--- BAD, must be first statement
  endfunction
endclass

module t;
  initial begin
    spi_reg_block test = new;
    $finish;
  end
endmodule
