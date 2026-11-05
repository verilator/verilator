// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// 'Class::method()' calls that class's implementation of a virtual function, not an override

class Base;
  virtual function int f();
    return 1;
  endfunction
  virtual task t(output int o);
    o = 1;
  endtask
  function int callSelf();
    return Base::f();  // Names its own class
  endfunction
endclass

class Mid extends Base;
  virtual function int f();
    return 2;
  endfunction
endclass

class Top extends Mid;
  virtual function int f();
    return 3;
  endfunction
  virtual task t(output int o);
    o = 3;
  endtask
  function int callf();
    return Base::f();  // Skips Mid::f
  endfunction
  task callt(output int o);
    Base::t(o);
  endtask
endclass

// Parameterized extends
class PMid #(
    type T = int
) extends Base;
endclass

class PTop extends PMid #(int);
  virtual function int f();
    return 4;
  endfunction
  function int callf();
    return Base::f();
  endfunction
endclass

module t;
  initial begin
    automatic Top top = new;
    automatic PTop ptop = new;
    int o;
    `checkd(top.callSelf(), 1);
    `checkd(top.callf(), 1);
    top.callt(o);
    `checkd(o, 1);
    `checkd(ptop.callf(), 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
