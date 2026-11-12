// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Christopher Onyiuke
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package lib_pkg;
  class Base #(type T = int);
  endclass

  // Specializing Agent #(Driver) elaborates Driver, and through it Leaf, before the
  // parameterized pass has visited Leaf itself, so 'len' inherited from Mid has to be
  // imported while resolving the inline constraint.
  class Agent #(type DRV_T = int);
    DRV_T drv;
    function void build();
      drv = DRV_T::create();
    endfunction
  endclass
endpackage

package user_pkg;
  import lib_pkg::*;

  class Mid extends Base #(int);
    rand bit [14:0] len;
  endclass

  class Leaf extends Mid;
  endclass

  class Driver;
    Leaf item;
    static function Driver create();
      Driver d = new;
      return d;
    endfunction
    function int send(bit [14:0] want);
      item = new;
      return item.randomize() with {len == want;};
    endfunction
  endclass
endpackage

module t;
  import lib_pkg::*;
  import user_pkg::*;

  initial begin
    automatic Agent #(Driver) agent = new;
    agent.build();
    for (int i = 0; i < 20; ++i) begin
      automatic bit [14:0] want = 15'(i * 1237 + 3);
      automatic int ok = agent.drv.send(want);
      `checkd(ok, 1);
      `checkd(agent.drv.item.len, want);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
