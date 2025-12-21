// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define check(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: $time=%0t got='h%x exp='h%x\n", `__FILE__,`__LINE__, $time, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module top;

    logic clk = 0;
    always #5 clk = ~clk;

    int cnt = 0;
    always @(posedge clk) cnt <= cnt + 1;

    wire forcedVar = &cnt[2:1];
    wire sharedTerm = &cnt[2:1];
    wire otherVar = ~sharedTerm;

    initial begin
      repeat (50) begin
        @(posedge clk);
        `check(otherVar == ~forcedVar, 1);
      end

      force forcedVar = 1'b1;

      repeat (50) begin
        @(posedge clk);
        `check(otherVar == ~forcedVar, cnt[2] & cnt[1]);
      end

      release forcedVar;

      repeat (50) begin
        @(posedge clk);
        `check(otherVar == ~forcedVar, 1);
      end

      force forcedVar = 1'b0;

      repeat (50) begin
        @(posedge clk);
        `check(otherVar == ~forcedVar, ~cnt[2] | ~cnt[1]);
      end

      release forcedVar;

      repeat (50) begin
        @(posedge clk);
        `check(otherVar == ~forcedVar, 1);
      end


      $write("*-* All Finished *-*\n");
      $finish;
    end

    always @(sharedTerm or otherVar) begin
      `check(otherVar, ~sharedTerm);
    end

endmodule
