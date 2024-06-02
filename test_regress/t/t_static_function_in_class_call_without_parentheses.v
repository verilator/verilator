// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
  static int m_v;

  static function void set_v(int v);
    m_v = v;
  endfunction
  static function int get_v();
    // Let's see if referring to the implicit variable does not resolve into a call
    get_v = m_v;
  endfunction
endclass

module t();
  initial begin
    int v;

    Foo::set_v(3);
    // Check if a parenthesesless call to static method works
    v = Foo::get_v;
    if (v != 3) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
