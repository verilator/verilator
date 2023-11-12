// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Packet;
   rand int m_one;

   constraint cons { m_one > 0 && m_one < 2; }

   Packet other;

   task test1;
      // TODO Verilator ignores this setting currently, always returning 0 (constraint off)
      cons.constraint_mode(1);
      cons.constraint_mode(0);
      if (cons.constraint_mode() != 0) $stop;
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

      // IEEE: function void object[.constraint_identifier].constraint_mode(bit on_off);
      // IEEE: function int object.constraint_identifier.constraint_mode();

      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
      // TODO test that these control constraints as specified
      p.constraint_mode(0);
      p.constraint_mode(1);
      // Not legal to get current constraint_mode() value on a class-only call

      // TODO Verilator ignores this setting currently, always returning 0 (constraint off)
      // TODO test that these control constraints as specified
      p.cons.constraint_mode(1);
      p.cons.constraint_mode(0);
      if (p.cons.constraint_mode() != 0) $stop;

      // TODO Verilator ignores this setting currently, always returning 0 (constraint off)
      // TODO test that these control constraints as specified
      p.other = new;
      p.other.cons.constraint_mode(1);
      p.other.cons.constraint_mode(0);
      if (p.other.cons.constraint_mode() != 0) $stop;

      p.test1();

      // TODO for example way to test this, see t_randomize_rand_mode.v

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
