// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define checkf function void f(); $printtimescale; $display("%0t", $time); endfunction

package pkg;
  `checkf;
endpackage

checker CHK();
  `checkf;
endchecker

program PRG;
  `checkf;
endprogram

class CLS;
  static `checkf;
endclass

module mod;
  CHK chk();
  PRG prg();
  initial begin
    $printtimescale;
    $display("%0t", $time);

    pkg::f();
    chk.f();
    prg.f();
    CLS::f();

    $finish;
  end
endmodule

`timescale 1ns / 10ps
