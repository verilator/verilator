// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  int m_v;

  function new(int v);
    m_v = v;
  endfunction

  extern task add_in_fork_delayed(int delay, Foo arg);
endclass

task automatic Foo::add_in_fork_delayed(int delay, Foo arg);
  fork
    #delay m_v = m_v + arg.m_v;
  join_none
endtask

module t();
  initial begin
    Foo foo1, foo2;
    foo1 = new(1);
    foo2 = new(2);
    foo1.add_in_fork_delayed(10, foo2);
    #20;
    if (foo1.m_v != 3)
      $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
