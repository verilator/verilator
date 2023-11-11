// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int m_one;

   Packet other;

   task test1;
      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
      // TODO test that these control randomization as specified
      m_one.rand_mode(0);
      m_one.rand_mode(1);
      if (m_one.rand_mode() != 1) $stop;
   endtask

endclass

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new;
      v = p.randomize();
      if (v != 1) $stop;
`ifndef VERILATOR
      if (p.m_one != 1) $stop;
`endif

      // IEEE: function void object[.random_variable].rand_mode(bit on_off);
      // IEEE: function int object.random_variable.rand_mode();

      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
      // TODO test that these control randomization as specified
      p.rand_mode(0);
      p.rand_mode(1);
      // Not legal to get current rand() value on a class-only call

      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
      // TODO test that these control randomization as specified
      p.m_one.rand_mode(0);
      p.m_one.rand_mode(1);
      if (p.m_one.rand_mode() != 1) $stop;

      // TODO test can't redefine rand_mode

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
