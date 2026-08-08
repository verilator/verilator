// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// RAM and sequential regs: write-only retention with real storage.
module t (
  input logic       clk,
  input logic       we,
  input logic [3:0] addr,
  input logic [7:0] wdata
);

  logic [7:0] mem [0:15];
  logic [7:0] last_wdata;
  logic [3:0] last_addr;

  always_ff @(posedge clk) begin
    if (we) mem[addr] <= wdata;
    last_wdata <= wdata;
    last_addr  <= addr;
  end

endmodule
