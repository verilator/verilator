// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Foo;
endclass

class Bar extends Foo;
    int m_field = get_1();
    function int get_1();
        return 1;
    endfunction
endclass
