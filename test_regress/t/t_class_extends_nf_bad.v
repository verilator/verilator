// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package Pkg;
class otFound2;
endclass
endpackage

class IsFound;
endclass

class Cls extends IsNotFound;  // BAD: not found
endclass

class Cls2 extends Pkg::NotFound2;  // BAD: not found
endclass

module t (/*AUTOARG*/);
endmodule
