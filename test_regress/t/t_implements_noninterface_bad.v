// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class NotIcls;
endclass

class ClsBad1 implements NotIcls;
endclass

interface class Icls;
endclass

class ClsBad2 extends Icls;
endclass

module t (/*AUTOARG*/);
   Cls c;
endmodule
