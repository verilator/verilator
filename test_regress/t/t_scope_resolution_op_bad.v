// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Alexander Brylev.
// SPDX-License-Identifier: CC0-1.0

module mod #(integer PARAM = 1234);
endmodule

interface mod_if #(integer PARAM = 4321);
endinterface

module t;
  localparam integer MOD_PARAM = mod::PARAM;
  localparam integer IF_PARAM = mod_if::PARAM;
endmodule
