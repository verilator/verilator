// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef class Bar;
typedef Bar Baz;

module t;
    initial begin
        Bar::Qux::boo(1);
        Baz::Qux::boo(1);
        if (!Bar::Qux::finish) $stop;
        $write("*-* All Finished *-*\n");
        $finish;
    end
endmodule

class Foo #(type T);
    static logic finish = 0;
    static function void boo(input logic rec);
        if (rec) Bar::Qux::boo(0);
        finish = 1;
    endfunction
endclass

class Goo #(type T);
    function void goo();
        T::Qux::boo(1);
    endfunction
endclass

class Bar;
    typedef Foo#(Bar) Qux;
endclass
