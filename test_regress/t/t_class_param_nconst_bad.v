// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class Cls #(parameter PARAM = 12);
endclass

module t;

   Cls #(.PARAM($random)) c;  // Bad param name

endmodule
