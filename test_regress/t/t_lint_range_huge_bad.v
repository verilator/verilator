// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    output wire [32'hFFFF_FFFF:1] out0  // <--- Error: Huge
);
  assign out0 = 1;
  logic [1:32'hFFFF_FFFF] right_huge;  // <--- Error: Huge
  logic [64'hFFFF_FFFF_FFFF_FFF0:0] wide_huge;  // <--- Error: Huge
  logic [3:-1] neg_ok;
  logic [32'shFFFF_FFFF:1] signed_neg_ok;
endmodule
