// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// Soft constraints and 'dist' in an inline randomize() with.
//
// An inline constraint block joins the class's own constraints, so a soft or a
// soft dist written inline has to interact with them the same way a declared one
// would, and a 'disable soft' written inline has to reach them.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

class Plain;
  rand bit [7:0] x;
endclass

class WithSoftDist;
  rand bit [7:0] x;
  constraint c_dist { soft x dist {8'd5 := 1, 8'd8 := 1}; }
endclass

class WithHardDist;
  rand bit [7:0] x;
  constraint c_dist { x dist {8'd5 := 1, 8'd8 := 1}; }
endclass

module t;
  initial begin
    Plain p;
    WithSoftDist ws;
    WithHardDist wh;
    int free_draws, saw5, saw8;
    p = new;
    ws = new;
    wh = new;

    repeat (50) begin
      // Inline soft, compatible with an inline hard set
      `checkd(p.randomize() with {soft x == 8'd5; x inside {8'd5, 8'd9};}, 1)
      `checkd(p.x, 8'd5)

      // Inline soft dist overridden by an inline hard constraint
      `checkd(p.randomize() with {soft x dist {8'd5 := 1, 8'd8 := 1}; x == 8'd9;}, 1)
      `checkd(p.x, 8'd9)

      // A declared soft dist gives way to an inline hard constraint
      `checkd(ws.randomize() with {x == 8'd9;}, 1)
      `checkd(ws.x, 8'd9)

      // An inline 'disable soft' reaches the declared soft dist
      `checkd(ws.randomize() with {disable soft x;}, 1)
      if (ws.x != 8'd5 && ws.x != 8'd8) free_draws++;

      // A declared hard dist keeps its set under an inline soft that agrees
      `checkd(wh.randomize() with {soft x == 8'd5;}, 1)
      `checkd(wh.x, 8'd5)

      // ... and gives the draw back once the soft is out of the way
      `checkd(wh.randomize(), 1)
      if (wh.x == 8'd5) saw5++;
      if (wh.x == 8'd8) saw8++;
    end

    `checkd(free_draws > 0, 1)
    `checkd(saw5 > 0, 1)
    `checkd(saw8 > 0, 1)

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
