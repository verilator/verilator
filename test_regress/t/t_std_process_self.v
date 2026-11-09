// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// Earlier covergroup or randomize() must not stop later unqualified std:: names (#9085)
class Rnd;
  rand bit [3:0] x;
  function void roll();
    if (randomize() != 1) $stop;
  endfunction
endclass

module cg_mod;
  bit clk;
  logic [1:0] v;
  covergroup cg @(posedge clk);
    coverpoint v;
  endgroup
  cg c = new;
endmodule

class Foo;
  static task do_something();
`ifdef USE_STD_PREFIX
    std::process p;
`else
    process p;
`endif
    p = process::self();
  endtask
  static function void do_others();
`ifdef USE_STD_PREFIX
    std::semaphore s;
    std::mailbox #(int) m;
`else
    semaphore s;
    mailbox #(int) m;
`endif
    s = new(1);
    m = new;
  endfunction
endclass

module t;
  cg_mod cgm ();
  initial begin
    Foo::do_something();
    Foo::do_others();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
