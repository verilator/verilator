// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int one;

   constraint a { one > 0 && one < 2; }

   task test1;
      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
      one.rand_mode(0);
      one.rand_mode(1);
      if (one.rand_mode() != 1) $stop;

      // TODO Verilator ignores this setting currently, always returning 0 (constraint off)
      a.constraint_mode(1);
      a.constraint_mode(0);
      if (a.constraint_mode() != 0) $stop;
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
      if (p.one != 1) $stop;
`endif

      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
      p.one.rand_mode(0);
      p.one.rand_mode(1);
      if (p.one.rand_mode() != 1) $stop;

      // TODO Verilator ignores this setting currently, always returning 0 (constraint off)
      p.a.constraint_mode(1);
      p.a.constraint_mode(0);
      if (p.a.constraint_mode() != 0) $stop;

      p.test1();

      // TODO test can't redefine constraint_mode
      // TODO test can't redefine rand_mode
      // TODO test can't call constraint_mode on non-constraint

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
