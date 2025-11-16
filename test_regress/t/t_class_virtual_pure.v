// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

virtual class VBase;
  pure virtual function int hello();
  // See Issue #6698; appears IEEE illegal
  // pure virtual task automatic fin();
  pure virtual task fin();
endclass

class VA extends VBase;
  virtual function int hello;
    return 2;
  endfunction
  virtual task automatic fin;
    $write("*-* All Finished *-*\n");
    $finish;
  endtask
endclass

module t;
  initial begin
    VA va;
    va = new;
    if (va.hello() != 2) $stop;
    va.fin();
  end
endmodule
