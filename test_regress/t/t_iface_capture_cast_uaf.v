// DESCRIPTION: Verilator: interface typedef capture use-after-free (issue #8492)
//
// The cast `if_inst.RFTag'(0)` is freed when the localparam is folded to a
// constant; the second `mbox` specialization must not read it again.
// This was a heap-use-after-free, caught by --enable-dev-asan builds.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

interface mbox_if #(parameter int WIDTH = 0);
  typedef struct packed {
    logic [1:0] tag;
    logic [WIDTH-1:0] addr;
  } RFTag;
endinterface

module mbox #(parameter int WIDTH = 0);
  mbox_if #(WIDTH) if_inst ();
  localparam logic [WIDTH+2:0] TAG_ZERO = {1'b1, if_inst.RFTag'(0)};
endmodule

module top;
  mbox #(.WIDTH(14)) u_mbox ();
  mbox #(.WIDTH(12)) u_mbox2 ();
endmodule
