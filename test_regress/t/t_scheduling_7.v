// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Alias type check error test.
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

static int counter = 0;

task wait_for_nba_region;
  static int nba;
  static int next_nba;
  next_nba++;
  nba <= next_nba;
  @(nba);
  counter++;
endtask

class Foo;
  task run_phases();
    repeat (2) begin
      fork
        if ($c(1)) wait_for_nba_region();
      join_none
    end
  endtask
endclass

module top;
  initial begin
    static Foo p = new;
    p.run_phases();
    #1;
    if (counter != 2) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
