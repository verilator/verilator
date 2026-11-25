// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// A disabled block whose compare the solver can't lower still compiles.
class frame_cmode_off_randidx;
  rand bit [7:0] x;
  rand bit [7:0] frame[2];
  bit [7:0] target[8][2];
  rand int idx;
  constraint d { x == 8'd7; }
  constraint c { frame == target[idx]; }
endclass

// The same block left on: a supported compare still expands.
class frame_cmode_gated;
  rand bit [7:0] x;
  rand bit [7:0] frame[2];
  rand bit [7:0] target[8][2];
  rand int idx;
  constraint d { x == 8'd7; }
  constraint c { idx == 3; frame == target[idx]; }
  function new();
    target[3][0] = 8'h55;
    target[3][1] = 8'h66;
  endfunction
endclass

module t;
  initial begin
    frame_cmode_off_randidx cmoff_obj;
    frame_cmode_gated cmgate_obj;
    int randomize_result;

    cmoff_obj = new;
    cmoff_obj.c.constraint_mode(0);
    randomize_result = cmoff_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cmoff_obj.x, 7);

    cmgate_obj = new;
    cmgate_obj.c.constraint_mode(1);
    randomize_result = cmgate_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cmgate_obj.idx, 3);
    `checkd(cmgate_obj.frame == cmgate_obj.target[3], 1);
    cmgate_obj.c.constraint_mode(0);
    randomize_result = cmgate_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cmgate_obj.x, 7);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
