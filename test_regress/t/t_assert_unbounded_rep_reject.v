// DESCRIPTION: Verilator: reject a failed active unbounded consecutive repetition
// SPDX-FileCopyrightText: 2026 Madhusudan K
// SPDX-License-Identifier: CC0-1.0

module t;
  logic clk = 0;
  logic psel = 0;
  logic paddr = 0;
  logic pready = 0;
  logic psel_no_endpoint = 0;
  logic paddr_no_endpoint = 0;
  logic pready_no_endpoint = 0;
  int failures = 0;
  int no_endpoint_failures = 0;

  always #5 clk = ~clk;

    // The address changes before the sampled pready endpoint.  The active
    // [*1:$] thread must reject this attempt.
  assert property (@(posedge clk)
    $rose(psel) |->
    ($rose(psel) ##1 ((!$changed(paddr))[*1:$] ##0 (pready == 1))))
  else failures++;

    // The repetition must also reject when paddr changes before pready ever
    // becomes true; a missing endpoint cannot repair the broken repetition.
  assert property (@(posedge clk)
    $rose(psel_no_endpoint) |->
    ($rose(psel_no_endpoint) ##1 ((!$changed(paddr_no_endpoint))[*1:$]
                                  ##0 (pready_no_endpoint == 1))))
  else no_endpoint_failures++;

  initial begin
    #12 psel = 1;
    psel_no_endpoint = 1;
    #20 paddr = 1;
    paddr_no_endpoint = 1;
    pready = 1;
    #20;
    if (failures != 1 || no_endpoint_failures != 1)
      $fatal(1, "expected one failure in each assertion, got %0d and %0d",
             failures, no_endpoint_failures);
    $write("PASS\n");
    $finish;
  end
endmodule
