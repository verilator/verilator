// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand bit [65:0] m_wideQueue[$];

  function new;
    m_wideQueue = '{3{0}};
  endfunction

  constraint int_queue_c {
    m_wideQueue[0] == 0;
    m_wideQueue[1] == 1;
    m_wideQueue[2] == 2;
  }
  function void self_check();
    if (m_wideQueue[0] != 0) $stop;
    if (m_wideQueue[1] != 1) $stop;
    if (m_wideQueue[2] != 2) $stop;
  endfunction
endclass

module t;
  int success;
  initial begin
    Foo foo = new;
    success = foo.randomize();
    if (success != 1) $stop;
    foo.self_check();

    $display("Queue: %p", foo.m_wideQueue);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
