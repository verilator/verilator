// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);
  // AstLet and AstProperty are also NodeFTasks, but lets are substituted earlier and properties should be "used" by their asserts so also not deadified
  let nclk = ~clk;
  assert property (@(posedge clk) 1);

  function void livefunc();
  endfunction
  task livetask;
  endtask
  // Tasks/functions that are called somewhere will not be deadified
  initial begin
    livefunc();
    livetask();
    $finish;
  end

  // These should be deadified
  task deadfunc();
    deeptask2();
  endtask
  task deadtask;
    deeptask1();
  endtask
  // A chain of dead tasks calling each other to ensure V3Dead can remove chained dead tasks
  task deeptask1;
    deeptask2();
  endtask
  task deeptask2;
    deeptask3();
  endtask
  task deeptask3;
    deeptask4();
  endtask
  task deeptask4;
  endtask
endmodule
