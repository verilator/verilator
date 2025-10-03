// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class base_reg_block;
  function new(string name);
  endfunction

  function string build_coverage();
    return "";
  endfunction
endclass

class spi_reg_block extends base_reg_block;
  function new();
    super.new(build_coverage());
  endfunction
endclass

module hvl_top;
  initial begin
    spi_reg_block test = new;
    $finish;
  end
endmodule
