// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// issue #5977: class-scoped typedef in parameterized class should resolve when
// referenced through a module typedef alias.

package axi_test;
  class axi_ax_beat #(
      parameter AW = 32,
      parameter IW = 8,
      parameter UW = 1
  );
    rand logic [IW-1:0] ax_id = '0;
    rand logic [AW-1:0] ax_addr = '0;
    rand logic [UW-1:0] ax_user = '0;
  endclass

  class axi_driver #(
      parameter int AW = 32,
      parameter int IW = 8,
      parameter int UW = 1
  );
    typedef axi_ax_beat#(
        .AW(AW),
        .IW(IW),
        .UW(UW)
    ) ax_beat_t;
  endclass
endpackage

module t;
  typedef axi_test::axi_driver#(
      .AW(64),
      .IW(6),
      .UW(2)
  ) drv_t;

  initial begin
    automatic drv_t::ax_beat_t aw_beat = new;
    automatic drv_t::ax_beat_t ar_beat = new;

    aw_beat.ax_addr = 64'h1234;
    ar_beat.ax_addr = aw_beat.ax_addr + 64'd1;
    if (ar_beat.ax_addr != 64'h1235) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
