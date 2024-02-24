// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface class Icls1;
   pure virtual function int icfboth;
endclass

interface class Icls2;
   pure virtual function int icfboth;
endclass

interface class IclsBoth extends Icls1, Icls2;
   // Bad collision on icfboth
endclass

class Cls implements IclsBoth;
endclass


// This is not a collision - diamond
interface class Ibase;
   pure virtual function int fn();
endclass

interface class Ic1 extends Ibase;
   pure virtual function int fn1();
endclass

interface class Ic2 extends Ibase;
   pure virtual function int fn2();
endclass

interface class Ic3 extends Ic1, Ic2;
endclass


module t (/*AUTOARG*/);
   Cls c;
endmodule
