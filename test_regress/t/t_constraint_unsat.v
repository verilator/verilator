// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand bit [7:0] addr;
  rand bit [7:0] data;

  constraint addr_range { addr < 127; }
  constraint data_range { data > 10 && data < 200; }

  function void check(bit [7:0] a, bit [7:0] d);
    /* verilator lint_off WIDTHTRUNC */
    if (!randomize() with { addr == a; data == d; }) begin
    /* verilator lint_on WIDTHTRUNC */
      $display("Randomization failed.");
    end
  endfunction
endclass

class TestConflict;
  rand bit [7:0] x;

  constraint c1 { x > 100; }
  constraint c2 { x < 50; }

  function bit try_randomize();
    /* verilator lint_off WIDTHTRUNC */
    return randomize();
    /* verilator lint_on WIDTHTRUNC */
  endfunction
endclass

module t_constraint_unsat;
  initial begin
    Packet pkt;
    TestConflict tc;

    pkt = new;

    // Test: Valid randomization
    $display("\n=== Test: Valid constraints ===");
    pkt.check(50, 100);

    // Test: addr out of range
    $display("\n=== Test: addr out of range ===");
    pkt.check(128, 18);

    // Test: data out of range (too small)
    $display("\n=== Test: data out of range (too small) ===");
    pkt.check(100, 5);

    // Test: data out of range (too large)
    $display("\n=== Test: data out of range (too large) ===");
    pkt.check(100, 250);

    // Test: Both constraints violated
    $display("\n=== Test: Both constraints violated ===");
    pkt.check(200, 5);

    // Test: Conflicting constraints
    $display("\n=== Test: Conflicting constraints (x > 100 && x < 50) ===");
    tc = new;
    if (!tc.try_randomize()) begin
      $display("Expected failure: conflicting constraints detected");
    end
    else begin
      $display("ERROR: Should have failed with conflicting constraints");
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
