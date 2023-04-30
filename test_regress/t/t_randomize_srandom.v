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

class Foo;
endclass

class Bar extends Foo;
   bit [63:0] m_sum;
   rand int m_r;
   function void hash_init();
      m_sum = 64'h5aef0c8d_d70a4497;
   endfunction
   function void hash(int res);
      $display("  res %x", res);
      m_sum = {32'h0, res} ^ {m_sum[62:0], m_sum[63] ^ m_sum[2] ^ m_sum[0]};
   endfunction

   function void this_srandom(int seed);
      this.srandom(seed);
   endfunction

   function bit [63:0] test2;
      $display("  init for seeded randomize");
      hash_init;
      $display("%d", m_r);
      hash(m_r);
      return m_sum;
   endfunction
endclass

module t(/*AUTOARG*/);

   Cls ca;
   Cls cb;
   Bar b1;
   Bar b2;

   bit [63:0] sa;
   bit [63:0] sb;

   initial begin
      // Each class gets different seed from same thread,
      // so the randomization should be different
      $display("New");
      ca = new;
      cb = new;
      b1 = new;
      b2 = new;

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

      $display("this.srandom - Bar class");
      b1.this_srandom(1);
      b2.this_srandom(2);
      void'(b1.randomize());
      void'(b2.randomize());
      sa = b1.test2;
      sb = b2.test2;
      `checkne(sa, sb);

      b1.this_srandom(3);
      b2.this_srandom(3);
      void'(b1.randomize());
      void'(b2.randomize());
      sa = b1.test2;
      sb = b2.test2;
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
