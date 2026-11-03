// DESCRIPTION: Verilator: reject a failed active unbounded consecutive repetition
// SPDX-FileCopyrightText: 2026 Madhusudan K
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv, expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

`ifdef TEST_IMPURE_ENDPOINT
module t;
  logic clk = 0;
  logic start = 0;
  logic a = 1;
  int calls = 0;

  function logic endpoint();
    calls++;
    return 0;
  endfunction

  always #5 clk = ~clk;

  assert property (@(posedge clk) start |-> a[*1:$] ##0 endpoint());
endmodule
`else
module t;
  logic clk = 0;
  logic psel = 0;
  logic paddr = 0;
  logic pready = 0;
  logic psel_no_endpoint = 0;
  logic paddr_no_endpoint = 0;
  logic pready_no_endpoint = 0;
  logic range_start = 0;
  logic range_x = 0;
  logic range_a = 0;
  logic range_b = 0;
  int failures = 0;
  int no_endpoint_failures = 0;
  int range_passes = 0;
  int range_failures = 0;
  time failure_time = 0;
  time no_endpoint_failure_time = 0;

  always #5 clk = ~clk;

  // The address changes before the sampled pready endpoint.  The active
  // [*1:$] thread must reject this attempt.
  assert property (@(posedge clk)
    $rose(psel) |->
    ($rose(psel) ##1 ((!$changed(paddr))[*1:$] ##0 (pready == 1))))
  else begin
    failures++;
    failure_time = $time;
  end

  // The repetition must also reject when paddr changes before pready ever
  // becomes true; a missing endpoint cannot repair the broken repetition.
  assert property (@(posedge clk)
    $rose(psel_no_endpoint) |->
    ($rose(psel_no_endpoint) ##1 ((!$changed(paddr_no_endpoint))[*1:$]
                                  ##0 (pready_no_endpoint == 1))))
  else begin
    no_endpoint_failures++;
    no_endpoint_failure_time = $time;
  end

  // A later candidate of the ranged delay must remain viable after an
  // earlier candidate fails its unbounded repetition.
  assert property (@(posedge clk)
    range_start |-> ##[0:2] (range_x ##0 range_a[*1:$] ##0 range_b))
  range_passes++;
  else range_failures++;

  initial begin
    #10 range_start = 1;
    range_x = 1;
    range_a = 1;
    #10 range_start = 0;
    range_x = 0;
    range_a = 0;
    #10 range_x = 1;
    range_a = 1;
    range_b = 1;
    #10;
    `checkh(range_passes, 1);
    `checkh(range_failures, 0);
  end

  initial begin
    $assertvacuousoff(0);
    #12 psel = 1;
    psel_no_endpoint = 1;
    #20 paddr = 1;
    paddr_no_endpoint = 1;
    pready = 1;
    #20;
    `checkh(failures, 1);
    `checkh(failure_time, 35);
    `checkh(no_endpoint_failures, 1);
    `checkh(no_endpoint_failure_time, 35);
    $write("PASS\n");
    $finish;
  end
endmodule
`endif
