// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

// TODO Verilator ignores this setting currently, always returning 1 (rand on)
`ifdef VERILATOR
 `define checkh_vlt1(gotv,expv) `checkh(gotv,1)
`else
 `define checkh_vlt1(gotv,expv) `checkh(gotv,expv)
`endif

class Packet;
   rand int m_one;
   rand int m_two;

   task test1;
      m_one.rand_mode(0);
      `checkh_vlt1(m_one.rand_mode(), 0);
      m_two.rand_mode(0);
      `checkh_vlt1(m_two.rand_mode(), 0);
      verify(0, 0);

      m_one.rand_mode(0);
      `checkh_vlt1(m_one.rand_mode(), 0);
      m_two.rand_mode(1);
      `checkh_vlt1(m_two.rand_mode(), 1);
      verify(0, 1);
   endtask

   task verify(int mode_one, int mode_two);
      bit one_ne10 = '0;
      bit two_ne10 = '0;
      int v;
      // TODO Verilator ignores this setting currently, always returning 1 (rand on)
`ifndef VERILATOR
      if (m_one.rand_mode() != mode_one) $stop;
      if (m_two.rand_mode() != mode_two) $stop;
`else
      if (m_one.rand_mode() != 1) $stop;
      if (m_two.rand_mode() != 1) $stop;
`endif
      for (int i = 0; i < 20; ++i) begin
	 m_one = 10;
	 m_two = 10;
	 v = randomize();
	 if (m_one != 10) one_ne10 = 1'b1;
	 if (m_two != 10) two_ne10 = 1'b1;
`ifdef TEST_VERBOSE
	 $display("one=%0d(rand_mode=%0d) two=%0d(rand_mode=%0d)",
		  m_one, mode_one, m_two, mode_two);
`endif
      end
      if (mode_one != 0 && !one_ne10) $stop;
      if (mode_two != 0 && !two_ne10) $stop;
`ifndef VERILATOR
      if (mode_one == 0 && one_ne10) $stop;
      if (mode_two == 0 && two_ne10) $stop;
`endif
   endtask

endclass

module t (/*AUTOARG*/);

   Packet p;

   int v;

   initial begin
      p = new;

      p.test1();

      // IEEE: function void object[.random_variable].rand_mode(bit on_off);
      // IEEE: function int object.random_variable.rand_mode();
      // Not legal to get current rand() value on a class-only call

      // We call rand_mode here too becuase the parsing is different from that
      // called from the class itself
      p.m_one.rand_mode(0);
      `checkh_vlt1(p.m_one.rand_mode(), 0);
      p.m_two.rand_mode(0);
      `checkh_vlt1(p.m_two.rand_mode(), 0);
      p.verify(0, 0);

      p.m_one.rand_mode(0);
      `checkh_vlt1(p.m_one.rand_mode(), 0);
      p.m_two.rand_mode(1);
      `checkh_vlt1(p.m_two.rand_mode(), 1);
      p.verify(0, 1);

      p.rand_mode(1);
      p.verify(1, 1);

      p.rand_mode(0);
      p.verify(0, 0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
