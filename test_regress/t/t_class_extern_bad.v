// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Base1;
   extern task nodef();
   extern task nodef();  // duplicate
endclass

task Base1::noproto();  // no such prototype
endtask

module t (/*AUTOARG*/);
endmodule
