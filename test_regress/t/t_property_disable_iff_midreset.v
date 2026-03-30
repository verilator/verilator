// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  bit rst = 0;
  bit start = 0;
  bit done = 0;

  int fails_a = 0;
  int fails_b = 0;

  // First launch at cyc==2 should be canceled by reset pulse in the middle.
  assert property (@(posedge clk) disable iff (rst) (cyc == 2) |-> ##2 done)
  else fails_a++;

  // Second launch at cyc==8 has no reset pulse in flight and should fail once.
  assert property (@(posedge clk) disable iff (rst) (cyc == 8) |-> ##2 done)
  else fails_b++;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    // Defaults
    start <= 0;
    done <= 0;

    if (cyc == 2) start <= 1;
    if (cyc == 8) start <= 1;

    // Mid-window reset pulse for first launch.
    if (cyc == 3) rst <= 1;
    if (cyc == 4) rst <= 0;

    if (cyc == 16) begin
      `checkd(fails_a, 0);
      `checkd(fails_b, 1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
