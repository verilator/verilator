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

class Class2;
    int x;
endclass;

class Base;
    int base_a;
endclass

class Derived extends Base;
    int derived_a;
endclass

class Base2;
    int base2_a;
endclass

class Derived2 extends Base2;
    int derived2_a;
    Class2 c2;
endclass;

class Base3;
    int base3_a;
endclass

interface class Iclass;
endclass

class Derived3 extends Base3 implements Iclass;
    int derived3_a;
endclass

interface class Iclass2;
endclass

class Derived4 implements Iclass2;
    int derived4_a;
endclass

module t;
    struct_t s;
    iface i1();
    iface2 i2();
    Class c;
    Derived d;
    Derived2 d2;
    Base2 b2;
    Derived3 d3;
    Iclass iclass;
    Derived4 d4;
    Iclass2 iclass2;

  initial begin
    c = new;
    c.i1 = i1;
    c.i2[0][0] = i2;
    d = new;
    d2 = new;
    d2.c2 = new;
    b2 = d2;
    d3 = new;
    iclass = d3;
    d4 = new;
    iclass2 = d4;

`ifdef DISPLAY_OBJECTS
    $display("struct: '%p'", s);
    $display("class: '%p'", c);
    $display("class from subclass: '%p'", d);
    $display("class from superclass: '%p'", b2);
    $display("class from interface: '%p'", iclass);
    $display("class from interface 2: '%p'", d4);
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
