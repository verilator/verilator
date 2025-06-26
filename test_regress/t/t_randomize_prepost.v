// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef enum int {
   RANDOMIZED = 20
} enumed_t;

class Base;
  int m_pre;
  rand enumed_t r;
  int m_post;

  function void pre_randomize;
    `checkd(m_pre, 0);
    `checkd(r, enumed_t'(0));
    `checkd(m_post, 0);
    m_pre = 10;
  endfunction

  function void post_randomize;
    `checkd(m_pre, 10);
    `checkd(r, RANDOMIZED);
    `checkd(m_post, 0);
    m_post = 30;
  endfunction
endclass

class Cls extends Base;
  int m_cpre;
  int m_cpost;
  function void pre_randomize;
     m_cpre = 111;
     super.pre_randomize();
  endfunction

  function void post_randomize;
     m_cpost = 222;
     super.post_randomize();
  endfunction
endclass

module t (/*AUTOARG*/);

  initial begin
    Cls c;
    int rand_result;

    c = new;
    rand_result = c.randomize();
    `checkd(rand_result, 1);
    `checkd(c.m_pre, 10);
    `checkd(c.m_cpre, 111);
    `checkd(c.r, RANDOMIZED);
    `checkd(c.m_post, 30);
    `checkd(c.m_cpost, 222);

    c = new;
    rand_result = c.randomize() with { r == RANDOMIZED; };
    `checkd(rand_result, 1);
    `checkd(c.m_pre, 10);
    `checkd(c.m_cpre, 111);
    `checkd(c.r, RANDOMIZED);
    `checkd(c.m_post, 30);
    `checkd(c.m_cpost, 222);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
