// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  int i;

  typedef struct packed {
    int i;
    i badi;  // Bad
  } struct_t;

  typedef union packed {
    // Bad
    logic [($bits(later) / 8)-1:0][7:0] bad_forward;
    logic [15:0] later;
  } forward_member_t;

endmodule
