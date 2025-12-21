// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class base;
  function new(string name);
    $display(name);
    if (name == "42") $finish;
  endfunction

  function string retstr();
    return $sformatf("%0d", $c("42"));
  endfunction
endclass

class derived extends base;
  function new();
    super.new(retstr());
  endfunction
endclass

module t;
  initial begin
    derived test = new;
  end
endmodule
