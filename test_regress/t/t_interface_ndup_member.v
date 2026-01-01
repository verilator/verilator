// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface backdoor_if;
  logic [15:0] signal1;
  logic [15:0] signal2;
  assign signal1 = t.child1.sub1.signal3;
  assign signal2 = t.child2.sub2.signal3;
  function int get_size_signal1();
    return $bits(signal1);
  endfunction
endinterface

module sub #(
    parameter DELAY = 10
) ();
  logic [15:0] signal3;
endmodule

package tests_pkg;
  class signal1_backdoor;
    virtual backdoor_if vif;
    virtual function int get_signal_size();
      return vif.get_size_signal1();
    endfunction
  endclass
endpackage

module child ();
  sub #(10) sub1 ();
  sub #(25) sub2 ();
endmodule

module t;
  child child1 ();
  child child2 ();
endmodule
