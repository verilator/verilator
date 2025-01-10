// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

class Cls1;
    rand bit b1;
    randc int b2;

    constraint raint2_bad { solve b1 before b2; }  // BAD no randc vars here
endclass

module t (/*AUTOARG*/);
endmodule
