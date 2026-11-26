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
    function int send_inline();
      item = new;
      // Inline random variable control references the inherited 'len' too.
      return item.randomize(len);
    endfunction
  endclass
endpackage

package items_pkg;
  class base_item;
    rand int x;
  endclass
  class item extends base_item;
  endclass

  class param_base #(type T = int);
    rand int y;
  endclass
  class param_mid extends param_base #(int);
    rand int z;
  endclass
  class param_item extends param_mid;
  endclass
endpackage

package seqs_pkg;
  class seq;
    function int apply_value(items_pkg::item it, int value);
      return it.randomize() with {x == local::value;};
    endfunction
    function int apply_param(items_pkg::param_item it, int value);
      return it.randomize() with {y == local::value; z == local::value + 1;};
    endfunction
  endclass
endpackage

module t;
  import lib_pkg::*;
  import user_pkg::*;

  initial begin
    automatic Agent #(Driver) agent = new;
    automatic items_pkg::item it = new;
    automatic items_pkg::param_item pit = new;
    automatic seqs_pkg::seq s = new;
    agent.build();
    for (int i = 0; i < 20; ++i) begin
      automatic bit [14:0] want = 15'(i * 1237 + 3);
      automatic int ok = agent.drv.send(want);
      automatic int ok_inline;
      `checkd(ok, 1);
      `checkd(agent.drv.item.len, want);
      ok_inline = agent.drv.send_inline();
      `checkd(ok_inline, 1);
    end
    for (int i = 0; i < 20; ++i) begin
      automatic int want = i * 7919 - 50000;
      `checkd(s.apply_value(it, want), 1);
      `checkd(it.x, want);
      `checkd(s.apply_param(pit, want), 1);
      `checkd(pit.y, want);
      `checkd(pit.z, want + 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
