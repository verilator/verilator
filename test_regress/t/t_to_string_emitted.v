// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

typedef struct {
    struct {
        int a;
    } s1;
    struct {
        int b;
    } s2[2][3];
    int x;
} struct_t;

interface iface;
    int y1;
endinterface

interface iface2;
    int y2;
endinterface

class Class;
    int z;
    virtual iface i1;
    virtual iface2 i2[1][1];
    struct {
        int a;
    } s1;
    struct {
        int b;
    } s2[2][3];
endclass

class Base;
    int a;
endclass

class Derived extends Base;
    int b;
endclass

module t;
    struct_t s;
    iface i1();
    iface2 i2();
    Class c;
    Derived d;

  initial begin
    c = new;
    c.i1 = i1;
    c.i2[0][0] = i2;
    d = new;

`ifdef DISPLAY_OBJECTS
    $display("'%p'", s);
    $display("'%p'", c);
    $display("'%p'", d);
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
