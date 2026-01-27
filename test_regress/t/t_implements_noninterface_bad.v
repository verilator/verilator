// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class NotIcls;
endclass

class ClsBad1 implements NotIcls;
endclass

interface class Icls;
endclass

class ClsBad2 extends Icls;
endclass

module t;
   ClsBad2 c;
endmodule
