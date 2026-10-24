// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef struct { int unsigned F; } t_s;
  localparam t_s S = '{F: 32'd7};
  localparam W = S;
endmodule
