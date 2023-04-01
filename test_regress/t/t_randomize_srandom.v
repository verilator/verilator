// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkeq(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkne(gotv,expv) do if ((gotv) === (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

class Cls;
   bit [63:0] m_sum;
   rand int m_r;
   function void hash_init();
      m_sum = 64'h5aef0c8d_d70a4497;
   endfunction
   function void hash(int res);
      $display("  res %x", res);
      m_sum = {32'h0, res} ^ {m_sum[62:0], m_sum[63] ^ m_sum[2] ^ m_sum[0]};
   endfunction

   function bit [63:0] test1();
      Cls o;
      // Affected by srandom
      $display("  init for randomize");
      hash_init;
      // TODO: Support this.randomize()
      o = this;
      void'(o.randomize());
      hash(m_r);
      void'(o.randomize());
      hash(m_r);
      return m_sum;
   endfunction

   function bit [63:0] test2(int seed);
      $display("  init for seeded randomize");
      hash_init;
      this.srandom(seed);
      void'(this.randomize());
      hash(m_r);
      return m_sum;
   endfunction

   function bit [63:0] test3(int seed);
      $display("  init for seeded randomize");
      hash_init;
      srandom(seed);
      void'(randomize());
      hash(m_r);
      return m_sum;
   endfunction
endclass

module t(/*AUTOARG*/);

   Cls ca;
   Cls cb;

   bit [63:0] sa;
   bit [63:0] sb;

   initial begin
      // Each class gets different seed from same thread,
      // so the randomization should be different
      $display("New");
      ca = new;
      cb = new;

      sa = ca.test1();
      sb = cb.test1();
      `checkne(sa, sb);  // Could false-fail 2^-32

      // Seed the classes to be synced
      $display("Seed");
      ca.srandom(123);
      cb.srandom(123);

      sa = ca.test1();
      sb = cb.test1();
      `checkeq(sa, sb);

      // Check using this
      $display("this.srandom");
      sa = ca.test2(1);
      sb = cb.test2(2);
      `checkne(sa, sb);

      sa = ca.test2(3);
      sb = cb.test2(3);
      `checkeq(sa, sb);

      // Check using direct call
      $display("srandom");
      sa = ca.test3(1);
      sb = cb.test3(2);
      `checkne(sa, sb);

      sa = ca.test3(3);
      sb = cb.test3(3);
      `checkeq(sa, sb);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
