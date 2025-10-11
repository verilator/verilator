// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package ipkg;
  typedef interface class iclass;

  interface class iclass;
    pure virtual function void doit();
  endclass
endpackage

package epkg;
  interface class cclass2 extends ipkg::iclass;
    pure virtual function void doit2();
  endclass

  class cclass implements cclass2;
    virtual function void doit();
      $display("doit");
    endfunction
    virtual function void doit2();
      $display("doit2");
    endfunction
  endclass
endpackage

module top;
  import epkg::*;

  initial begin
    automatic cclass c = new();
    c.doit();
    $finish;
  end
endmodule
