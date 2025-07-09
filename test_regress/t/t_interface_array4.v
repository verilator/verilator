// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface Ifc;
  logic req, grant;
  logic [7:0] addr, data;
endinterface

class Cls;
  virtual Ifc bus;
  int m_i;
  function new(virtual Ifc s, int i);
    bus = s;
    m_i = i;
  endfunction
  task request();
    bus.req <= 1'b1;
  endtask
  task wait_for_bus();
    @(posedge bus.grant);
  endtask
endclass

module devA (Ifc s);
endmodule
module devB (Ifc s);
endmodule

module top;
  Ifc s14[1:4] ();
  devA a1 (s14[1]);
  devB b1 (s14[2]);
  devA a2 (s14[3]);
  devB b2 (s14[4]);

  Ifc s65[6:5] ();
  devA a3 (s65[5]);
  devB b3 (s65[6]);

  initial begin
    Cls t14[1:4];
    Cls t65[6:5];
    t14[1] = new(s14[1], 1);
    t14[2] = new(s14[2], 2);
    t14[3] = new(s14[3], 3);
    t14[4] = new(s14[4], 4);
    t65[5] = new(s65[5], 5);
    t65[6] = new(s65[6], 6);
  end
endmodule
