// DESCRIPTION: Verilator: Tristate with non-blocking assignment to Z state
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__, `__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
  input clk
);

  int cyc;

  // verilator lint_off MULTIDRIVEN
  logic tribus;
  // verilator lint_on MULTIDRIVEN

  wire driver1_en = cyc[0];
  wire driver1_dat = cyc[1];
  always @(negedge clk) begin
    tribus <= driver1_en ? driver1_dat : 1'bz;
  end

  wire driver2_en = cyc[2];
  wire driver2_dat = cyc[3];
  always @(negedge clk) begin
    tribus <= driver2_en ? driver2_dat : 1'bz;
  end

  always @(posedge clk) begin
`ifdef TEST_VERBOSE
    $write("[%0t] cyc==%0d tb=%x (%x,%x) (%x,%x)\n", $time, cyc, tribus, driver1_en, driver1_dat,
           driver2_en, driver2_dat);
`endif
    cyc <= cyc + 1;
    if (cyc == 0) begin
      // Setup
    end else if (cyc < 50) begin
      if (!driver1_en && !driver2_en) begin
        `checkh(tribus, 1'bz);
      end else if (driver1_en && !driver2_en) begin
        `checkh(tribus, driver1_dat);
      end else if (!driver1_en && driver2_en) begin
        `checkh(tribus, driver2_dat);
      end else begin
        // Ignore conflict cases
      end
    end else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
