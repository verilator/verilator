// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

`timescale 1ns/1ps
// Test constant parameter slicing of unpacked arrays with various slice ranges.

module issue_desc #(
  parameter int els_p = 1,
  parameter int val_p [els_p+1:2],
  parameter int orig_els = 1
) ();
  // Drop the lowest index (2) in each recursion: slice [high:3]
  if (els_p > 1) begin : r
    issue_desc #(
      .els_p(els_p-1),
      .val_p(val_p[els_p+1:3]),
      .orig_els(orig_els)
    ) x();
  end
  initial begin
    int expected = orig_els - els_p + 1;
    if (val_p[2] !== expected) begin
      $error("DESC wrong value %0d expected %0d in %m", val_p[2], expected);
      $finish;
    end
    $display("%08x (desc %m)", val_p[2]);
  end
endmodule

module issue_rev #(
  parameter int els_p = 1,
  parameter int val_p [2:els_p+1],
  parameter int orig_els = 1
) ();
  // Drop the lowest index (2) in each recursion: slice [3:high]
  if (els_p > 1) begin : r
    issue_rev #(
      .els_p(els_p-1),
      .val_p(val_p[3:els_p+1]),
      .orig_els(orig_els)
    ) x();
  end
  initial begin
    int expected = orig_els - els_p + 1;
    if (val_p[2] !== expected) begin
      $error("REV wrong value %0d expected %0d in %m", val_p[2], expected);
      $finish;
    end
    $display("%08x (rev %m)", val_p[2]);
  end
endmodule

module issue_def #(
  parameter int els_p = 1,
  // Internal default fill is zero; the test overrides this with DEADBEEF.
  parameter int val_p [els_p+1:2] = '{default:0},
  parameter int orig_els = 1
) ();
  // Recursively slice off the lowest index (2)
  if (els_p > 1) begin : r
    issue_def #(
      .els_p(els_p-1),
      .val_p(val_p[els_p+1:3]),
      .orig_els(orig_els)
    ) x();
  end
  initial begin
    // Expect 32'hDEADBEEF when overridden by the top-level test.
    if (val_p[2] !== 32'hDEADBEEF) begin
      $error("DEF wrong value %0x expected DEADBEEF in %m", val_p[2]);
      $finish;
    end
    $display("%08x (def %m)", val_p[2]);
  end
endmodule

module t;
  // For els_p=5, the range [els_p+1:2] is [6:2].
  // Descending initializer: index 6=5,5=4,4=3,3=2,2=1.
  parameter int val_desc [6:2] = '{5,4,3,2,1};
  // Reverse slice initializer: ascending values on [2:6].
  parameter int val_rev  [2:6] = '{1,2,3,4,5};
  // Override for default-array test: all elements set to 32'hDEADBEEF on [6:2].
  parameter int val_def  [6:2] = '{default: 32'hDEADBEEF};

  issue_desc #(.els_p(5), .val_p(val_desc), .orig_els(5)) iss_desc();
  issue_rev  #(.els_p(5), .val_p(val_rev),  .orig_els(5)) iss_rev();
  issue_def  #(.els_p(5), .val_p(val_def),  .orig_els(5)) iss_def();

  initial begin
    #1;
    $write("*-* All Finished *-*\\n");
    $finish;
  end
endmodule
