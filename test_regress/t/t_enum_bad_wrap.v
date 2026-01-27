// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   typedef enum [1:0] {
                  PREWRAP = 2'd3,
                  WRAPPED
                  } wrap_t;

endmodule
