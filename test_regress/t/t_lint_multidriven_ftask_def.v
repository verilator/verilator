// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t(input wire clk, input wire reset, input wire request);
  // Writes in never-called task/function definitions are not executed
  // processes, so they must not count as the "other write" of MULTIDRIVEN,
  // no matter how many of them there are.

  logic foo;

  function void release_foo;
    foo <= 1'b0;
  endfunction

  function void request_foo;
    foo <= 1'b1;
  endfunction

  always_ff @(posedge clk) begin
    if (reset) foo <= 1'b0;
    else foo <= 1'b1;
  end

  logic bar;

  task automatic clear_bar;
    bar = 1'b0;
  endtask

  task automatic set_bar;
    bar = 1'b1;
  endtask

  always_comb begin
    if (reset) bar = 1'b0;
    else bar = 1'b1;
  end

  // Same, but the functions are actually called from the always_ff.  The
  // writes are applied at the call sites, which are in that same always_ff.

  logic baz;

  function void release_baz;
    baz <= 1'b0;
  endfunction

  function void request_baz;
    baz <= 1'b1;
  endfunction

  always_ff @(posedge clk) begin
    if (reset) baz <= 1'b0;
    else if (request) request_baz();
    else release_baz();
  end

endmodule
