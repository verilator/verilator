// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Foo;
  rand bit [65:0] m_wideUnpacked[3];

  constraint int_queue_c {
    m_wideUnpacked[0] == 0;
    m_wideUnpacked[1] == 1;
    m_wideUnpacked[2] == 2;
  }
  function void self_check();
    if (m_wideUnpacked[0] != 0) $stop;
    if (m_wideUnpacked[1] != 1) $stop;
    if (m_wideUnpacked[2] != 2) $stop;
  endfunction
endclass

module t;
  int success;
  initial begin
    automatic Foo foo = new;
    success = foo.randomize();
    if (success != 1) $stop;
    foo.self_check();

    $display("Unpacked: %p", foo.m_wideUnpacked);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
