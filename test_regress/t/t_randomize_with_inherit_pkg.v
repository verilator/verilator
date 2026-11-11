// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

package items;
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

package seqs;
  class seq;
    function int apply_value(items::item it, int value);
      return it.randomize() with {x == local::value;};
    endfunction
    function int apply_param(items::param_item it, int value);
      return it.randomize() with {y == local::value; z == local::value + 1;};
    endfunction
  endclass
endpackage

module t;
  initial begin
    automatic items::item it = new;
    automatic items::param_item pit = new;
    automatic seqs::seq s = new;
    `checkd(s.apply_value(it, 42), 1);
    `checkd(it.x, 42);
    `checkd(s.apply_param(pit, 7), 1);
    `checkd(pit.y, 7);
    `checkd(pit.z, 8);
    $display("*-* All Finished *-*");
    $finish;
  end
endmodule
