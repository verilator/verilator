// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Base1;
endclass

class Base2;
endclass

class Cls extends Base1, Base2;
endclass

module t;
endmodule
