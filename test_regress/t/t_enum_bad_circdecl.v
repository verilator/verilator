// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef enum bad_redecl;
  typedef enum bad_redecl [2:0] {VALUE} bad_redecl;

endmodule
