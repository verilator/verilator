// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Member;
  int x = 1;
endclass

class Base;
  int b = 2;
  int q[$];
  virtual function int get();
    return b;
  endfunction
endclass

class NeverVirt extends Base;
  Member m;
  function new();
    m = new;
  endfunction
  virtual function int get();
    return 3;
  endfunction
endclass

class NeverPlain;
  Member m;
  int q[$];
endclass

class Created extends Base;
  Member m;
  function new();
    super.new();
    m = new;
  endfunction
  virtual function int get();
    return 4;
  endfunction
endclass

module t;
  initial begin
    Base bh;
    Created c;
    Created c2;
    NeverVirt nv;
    NeverPlain np;
    c  = new;
    bh = c;
    if ($cast(nv, bh)) $stop;
    if (!$cast(c2, bh)) $stop;
    if (bh.get() != 4) $stop;
    c2 = new c;
    if (c2.get() != 4) $stop;
    if (c2.m.x != 1) $stop;
    if (np != null) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
