// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t(input wire clk, input wire reset);
  // A function definition is not a driver by itself, but a call to it is.
  // The reported other write must be the call site, not the function body.

  logic foo;

  function void release_foo;
    foo <= 1'b0;
  endfunction

  function void request_foo;
    foo <= 1'b1;
  endfunction

  always_ff @(posedge clk) request_foo();  // <--- Location of other write

  always_ff @(posedge reset) foo <= 1'b0;  // <--- Warning

  logic bar;

  task automatic set_bar;
    bar = 1'b1;
  endtask

  always_comb set_bar();  // <--- Location of other write

  always_comb bar = 1'b0;  // <--- Warning

endmodule
