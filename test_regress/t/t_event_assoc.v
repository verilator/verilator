// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  int stage;
  event e[int];
  event es[string];
  event ed[];
  event eq[$];
  event edd[][2];
  event eda[][int];

  initial begin
    @(e[3]);
    `checkd(stage, 1);
    stage = 2;
  end

  initial begin
    @(es["run_phase"]);
    `checkd(stage, 2);
    stage = 3;
  end

  initial begin
    ed = new[2];
    @(ed[1]);
    `checkd(stage, 3);
    stage = 4;
  end

  initial begin
    event ev;
    eq.push_back(ev);
    eq.push_back(ev);
    edd = new[2];
    @(eq[1]);
    eda = new[2];
    @(edd[1][0]);
    `checkd(stage, 4);
    stage = 5;
  end

  initial begin
    @(eq[$]);
    @(eda[1][7]);
    `checkd(stage, 5);
    stage = 6;
  end

  initial begin
    #1;
    stage = 1;
    ->e[3];
    #1;
    `checkd(stage, 2);
    #1;
    ->es["run_phase"];
    #1;
    `checkd(stage, 3);
    ->ed[1];
    #1;
    `checkd(stage, 4);
    ->eq[1];
    #1;
    ->edd[1][0];
    #1;
    `checkd(stage, 5);
    ->eq[1];
    #1;
    ->eda[1][7];
    #1;
    `checkd(stage, 6);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
