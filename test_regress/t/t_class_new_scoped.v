// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

class Base;
  int m_ia = 10;
  function new(int i);
    m_ia = i;
  endfunction
endclass

class ClsNoArg extends Base;
  function new();
    super.new(5);
  endfunction : new
endclass

class ClsArg extends Base;
  function new(int i, int j);
    super.new(i + j);
  endfunction
endclass

class ClsParam #(int ADD = 100) extends Base;
  function new(int def = 42);
    super.new(def + ADD);
  endfunction
endclass

module t (/*AUTOARG*/);
  initial begin
    Base b;
    ClsNoArg c1;
    ClsArg c2;
    ClsParam#(100) c3;
    ClsParam#(200) c4;

    c1 = new;
    `checkd(c1.m_ia, 5);
    b = ClsNoArg::new;
    `checkd(b.m_ia, 5);

    c2 = new(20, 1);
    `checkd(c2.m_ia, 21);
    b = ClsArg::new(20, 1);
    `checkd(b.m_ia, 21);

    c3 = new(33);
    `checkd(c3.m_ia, 133);
    b = ClsParam#(100)::new(33);
    `checkd(b.m_ia, 133);

    c4 = new(44);
    `checkd(c4.m_ia, 244);
    b = ClsParam#(200)::new(44);
    `checkd(b.m_ia, 244);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
