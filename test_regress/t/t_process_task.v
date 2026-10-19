// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkd(gotv, expv) \
  do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d\n", `__FILE__, `__LINE__, (gotv), (expv)); $stop; end while (0)
// verilog_format: on

module t;
  std::process proc;
  logic clk = 0;
  logic b = 0;
  bit child_ran = 0;

  always #1 clk = ~clk;

  task kill_me_after_1ns();
    fork
      #1 proc.kill();
      #3 begin
        child_ran = 1;
      end
    join_none
  endtask

  initial begin
    #5;
    // process::kill() must terminate descendants
    `checkd(child_ran, 1'b0);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  always @(posedge clk) begin
    if (!b) begin
      proc = std::process::self();
      kill_me_after_1ns();
      b = 1;
    end
    else begin
      $stop;
    end
  end
endmodule
