// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  logic clk = 0;
  always #5 clk = ~clk;

  logic [7:0] data_ref;
  logic [7:0] data_test;

  default clocking cb @(posedge clk);
    output #0 data_ref;
    output #0 data_test;
  endclocking

  // =========================================================
  // Branch 1: Procedural ##0 (IEEE 1800-2023 14.11)
  // - Before clocking event: suspend until event fires
  // - After clocking event: continue without suspension
  // =========================================================

  // 1a: ##0 at time 0 -- event has not yet fired, must wait
  initial begin
    ##0;
    `checkd(int'($time), 5)
  end

  // 1b: ##0 after @(posedge clk) -- event already fired, no-op
  initial begin
    @(posedge clk);
    ##0;
    `checkd(int'($time), 5)
  end

  // 1c: Multiple consecutive ##0 all resolve at same time
  initial begin
    ##0;
    ##0;
    ##0;
    `checkd(int'($time), 5)
  end

  // 1d: ##0 followed by ##1 -- verify cycle counting still works
  initial begin
    ##0;
    `checkd(int'($time), 5)
    ##1;
    `checkd(int'($time), 15)
  end

  // =========================================================
  // Branch 2: ##0 in synchronous drive (IEEE 1800-2023 14.11)
  // "shall have no effect, as if it were not present"
  // cb.data <= ##0 value  behaves same as  cb.data <= value
  // =========================================================

  // Drive both at the same posedge: one with ##0, one without.
  // If ##0 is truly "no effect", both signals update in the same cycle.
  always begin
    @(posedge clk);
    cb.data_ref <= 8'hAB;  // no ##0 -- baseline
    cb.data_test <= ##0 8'hAB;  // with ##0 -- should behave identically
    @(posedge clk);
    `checkd(data_test, data_ref)
    `checkd(data_test, 8'hAB)
    wait (0);
  end

  // =========================================================
  // Branch 3: ##0 in property/sequence context
  // a ##0 b = both a and b hold at the same clock tick
  //
  // =========================================================

  logic p = 0, q = 0;
  int cycle = 0;
  int assert_pass_count = 0;

  always @(posedge clk) begin
    cycle <= cycle + 1;
    p <= (cycle == 3);  // p=1 only at cycle 4
    q <= (cycle == 3);  // q=1 only at cycle 4
  end

  // Pass action block: only incremented on nonvacuous success
  assert property (@(posedge clk) p |-> (p ##0 q)) assert_pass_count++;
  else $error("Branch 3: assertion (p |-> p ##0 q) failed");

  // =========================================================
  // Completion
  // =========================================================

  initial begin
    #200;
    if (assert_pass_count == 0) begin
      $write("%%Error: assertion (p |-> p ##0 q) never passed non-vacuously\n");
      `stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
