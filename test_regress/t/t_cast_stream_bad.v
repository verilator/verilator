// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef byte bytes_t[$];

  logic [14:0] v15;
  logic [4:0] arr[3];
  bytes_t q;

  initial begin
    q = bytes_t'(v15);  // Bad: 15 bits are not whole bytes
    q = bytes_t'({>>{arr}});  // Bad: 15 bits are not whole bytes
  end

endmodule
