// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Each iteration of a loop reads the value of an NBA target from prior the time step

module t;
  bit clk;
  int cyc;
  int n = 3;

  int count;
  always @(posedge clk) for (int i = 0; i < n; ++i) count <= count + 1;
  always @(negedge clk) `checkh(count, cyc);

  int nested;
  always @(posedge clk) begin
    for (int i = 0; i < n; ++i) begin
      for (int j = 0; j < n; ++j) nested <= nested + i + j;
    end
  end
  always @(negedge clk) `checkh(nested, 4 * cyc);

  bit [7:0] shift = 8'h81;
  always @(posedge clk) for (int i = 0; i < n; ++i) shift[i+1] <= shift[i];
  always @(negedge clk) begin
    if (cyc == 1) `checkh(shift, 8'h83);
    if (cyc == 2) `checkh(shift, 8'h87);
    if (cyc == 3) `checkh(shift, 8'h8f);
  end

  // Read prior the loop that writes
  int prior;
  always @(posedge clk) begin
    int tmp;
    tmp = prior;
    for (int i = 0; i < n; ++i) prior <= tmp + i + 1;
  end
  always @(negedge clk) `checkh(prior, 3 * cyc);

  // Read and write in separate loops
  int split;
  always @(posedge clk) begin
    int sum;
    sum = 0;
    for (int i = 0; i < n; ++i) sum += split + 1;
    for (int i = 0; i < n; ++i) split <= sum + i;
  end
  always @(negedge clk) begin
    if (cyc == 1) `checkh(split, 5);
    if (cyc == 2) `checkh(split, 20);
    if (cyc == 3) `checkh(split, 65);
  end

  initial begin
    repeat (3) begin
      #1 clk = 1;
      ++cyc;
      #1 clk = 0;
    end
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
