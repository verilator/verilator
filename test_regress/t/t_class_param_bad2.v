// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

class Cls #(type PARAMB);
endclass

module t (/*AUTOARG*/);

   Cls c;  // Missing type param

endmodule
