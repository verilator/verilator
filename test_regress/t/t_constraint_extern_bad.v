// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Packet;
   extern constraint missing_bad;
endclass

constraint Packet::missing_extern { }

module t;
endmodule
