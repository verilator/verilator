// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module sub_a;
  int x = b.x;
endmodule

module sub_b;
  int x = a.x;
endmodule

package p1;
  int a = p2::b;
endpackage

package p2;
  int b = p1::a;
endpackage

module t;
  sub_a a();
  sub_b b();

  typedef class B;

  class A;
    static int a = B::b;
  endclass

  class B;
    static int b = A::a;
  endclass

  class FCycle;
    static int a = fa();
    static int b = fb();
    static function int fa();
      return b;
    endfunction
    static function int fb();
      return a;
    endfunction
  endclass

  initial begin
    // Intentional static-init cycle; this must not crash the compiler/runtime.
    $display("dot-cycle a.x=%0d b.x=%0d", a.x, b.x);
    $display("pkg-cycle p1::a=%0d p2::b=%0d", p1::a, p2::b);
    $display("func-cycle FCycle::a=%0d FCycle::b=%0d", FCycle::a, FCycle::b);
    $display("A::a=%0d B::b=%0d", A::a, B::b);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
