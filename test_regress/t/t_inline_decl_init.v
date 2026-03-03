// DESCRIPTION: Verilator: Test that inline declaration-with-initialization
// inside always blocks produces correct values.
//
// Bug: Verilator treats these as IMPLICITSTATIC, evaluating the initializer
// only once, so the variable retains stale values from the first evaluation
// when the index or inputs change.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t(
  input clk
);

  typedef struct packed {
    logic        valid;
    logic [7:0]  opcode;
    logic [15:0] data;
  } uop_t;

  localparam int QUEUE_SIZE = 4;

  uop_t queue [QUEUE_SIZE-1:0];

  // Fill the queue with distinct non-zero values
  initial begin
    queue[0] = '{valid: 1'b1, opcode: 8'hAA, data: 16'h1234};
    queue[1] = '{valid: 1'b1, opcode: 8'hBB, data: 16'h5678};
    queue[2] = '{valid: 1'b0, opcode: 8'hCC, data: 16'h9ABC};
    queue[3] = '{valid: 1'b1, opcode: 8'hDD, data: 16'hDEF0};
  end

  // =========================================================
  // Test 1: Struct inline init in for-loop (varying index)
  //
  //   The initializer `queue[i]` must re-evaluate each iteration.
  //   With IMPLICITSTATIC, it evaluates once at i=0 and is reused.
  // =========================================================

  uop_t test1_bug [QUEUE_SIZE-1:0];
  always_comb begin
    for (integer i = 0; i < QUEUE_SIZE; i = i + 1) begin
      uop_t e = queue[i];  // BUG: static — only evaluates at i=0
      test1_bug[i] = e;
    end
  end

  uop_t test1_ref [QUEUE_SIZE-1:0];
  always_comb begin
    for (integer i = 0; i < QUEUE_SIZE; i = i + 1) begin
      uop_t e;
      e = queue[i];         // OK: procedural assignment each iteration
      test1_ref[i] = e;
    end
  end

  // =========================================================
  // Test 2: reg[range] inline init in for-loop
  // =========================================================

  logic [7:0] mem [0:3];
  initial begin
    mem[0] = 8'h11;
    mem[1] = 8'h22;
    mem[2] = 8'h33;
    mem[3] = 8'h44;
  end

  logic [7:0] test2_bug [0:3];
  always_comb begin
    for (integer i = 0; i < 4; i = i + 1) begin
      reg [7:0] v = mem[i];  // BUG: static
      test2_bug[i] = v;
    end
  end

  logic [7:0] test2_ref [0:3];
  always_comb begin
    for (integer i = 0; i < 4; i = i + 1) begin
        reg [7:0] v;
        v = mem[i];
        test2_ref[i] = v;
    end
  end

  // =========================================================
  // Test 3: Dynamic select — struct inline init with sel changing
  //
  //   sel changes on each clock cycle.  The inline init should
  //   track the new sel value.
  // =========================================================

  logic [1:0] sel;
  initial sel = 0;

  always_ff @(posedge clk)
    sel <= sel + 1;

  uop_t test3_bug;
  always_comb begin
    uop_t e = queue[sel];  // BUG when sel changes
    test3_bug = e;
  end

  uop_t test3_ref;
  always_comb begin
    uop_t e;
    e = queue[sel];
    test3_ref = e;
  end

  // =========================================================
  // Test 4: Bare logic inline init with dynamic expr
  // =========================================================

  logic test4_bug;
  always_comb begin
    logic flag = queue[sel].valid;  // BUG when sel changes
    test4_bug = flag;
  end

  logic test4_ref;
  always_comb begin
    logic flag;
    flag = queue[sel].valid;
    test4_ref = flag;
  end

  // =========================================================
  // Checker
  // =========================================================

  int cycle;
  initial cycle = 0;
  int fail_count;
  initial fail_count = 0;

  always @(posedge clk) begin
    cycle <= cycle + 1;

    // ---- Test 1: for-loop struct ----
    for (integer i = 0; i < QUEUE_SIZE; i = i + 1) begin
      if (test1_bug[i] !== test1_ref[i]) begin
        $display("FAIL Test1 for-loop[%0d]: inline=%h split=%h",
                  i, test1_bug[i], test1_ref[i]);
        fail_count = fail_count + 1;
      end
    end

    // ---- Test 2: for-loop reg[range] ----
    for (integer i = 0; i < 4; i = i + 1) begin
      if (test2_bug[i] !== test2_ref[i]) begin
        $display("FAIL Test2 for-loop[%0d]: inline=%h split=%h",
                  i, test2_bug[i], test2_ref[i]);
        fail_count = fail_count + 1;
      end
    end

    // ---- Test 3: dynamic select struct ----
    if (test3_bug !== test3_ref) begin
      $display("FAIL Test3 dynamic sel=%0d: inline=%h split=%h",
                sel, test3_bug, test3_ref);
      fail_count = fail_count + 1;
    end

    // ---- Test 4: dynamic select bare logic ----
    if (test4_bug !== test4_ref) begin
      $display("FAIL Test4 dynamic sel=%0d: inline=%b split=%b",
                sel, test4_bug, test4_ref);
      fail_count = fail_count + 1;
    end

    // Sanity: verify reference values are meaningful
    if (test1_ref[0] === 25'h0 || test1_ref[1] === 25'h0) begin
      $display("FAIL sanity: ref arrays not initialized");
      fail_count = fail_count + 1;
    end

    if (fail_count > 0) begin
      $display("*** FAILED: %0d mismatches in cycle %0d ***", fail_count, cycle);
      $stop;
    end

    // Run for a few cycles so dynamic sel hits multiple values
    if (cycle >= 4) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
