// DESCRIPTION: Verilator: Test assignment patterns as comparison operands
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t;

  // Fixed-size array comparison
  int arr4[4];
  typedef int arr4_t[4];

  // Queue comparison
  int q[$];
  int sub[$];

  // Struct comparison
  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } pair_t;

  pair_t p1;

  // Nested: array of structs
  pair_t parr[2];

  // Different element types
  logic [31:0] wide_arr[3];
  byte byte_arr[2];

  initial begin
    // -------------------------------------------------------
    // 1. Fixed-size array: EQ with assignment pattern
    // -------------------------------------------------------
    arr4 = '{10, 20, 30, 40};
    if (arr4 == '{10, 20, 30, 40}) begin
      // expected
    end
    else begin
      $display("FAIL: arr4 == pattern");
      $stop;
    end

    // 2. Fixed-size array: NEQ with assignment pattern
    if (arr4 != '{10, 20, 30, 99}) begin
      // expected
    end
    else begin
      $display("FAIL: arr4 != pattern");
      $stop;
    end

    // 3. Pattern on LHS of comparison
    if ('{10, 20, 30, 40} == arr4) begin
      // expected
    end
    else begin
      $display("FAIL: pattern == arr4 (LHS)");
      $stop;
    end

    // 4. Pattern on LHS of NEQ
    if ('{10, 20, 30, 99} != arr4) begin
      // expected
    end
    else begin
      $display("FAIL: pattern != arr4 (LHS NEQ)");
      $stop;
    end

    // -------------------------------------------------------
    // 5. Queue: EQ with assignment pattern
    // -------------------------------------------------------
    q = '{10, 20, 30, 40, 50};
    sub = q[1:3];
    if (sub == '{20, 30, 40}) begin
      // expected
    end
    else begin
      $display("FAIL: queue slice == pattern");
      $stop;
    end

    // 6. Queue: NEQ with assignment pattern
    if (sub != '{20, 30, 99}) begin
      // expected
    end
    else begin
      $display("FAIL: queue slice != pattern");
      $stop;
    end

    // -------------------------------------------------------
    // 7. Struct: EQ with assignment pattern
    // -------------------------------------------------------
    p1 = '{a: 8'hAA, b: 8'h55};
    if (p1 == '{a: 8'hAA, b: 8'h55}) begin
      // expected
    end
    else begin
      $display("FAIL: struct == pattern");
      $stop;
    end

    // 8. Struct: NEQ with assignment pattern
    if (p1 != '{a: 8'hAA, b: 8'hFF}) begin
      // expected
    end
    else begin
      $display("FAIL: struct != pattern");
      $stop;
    end

    // -------------------------------------------------------
    // 9. Array of structs: EQ with nested pattern
    // -------------------------------------------------------
    parr[0] = '{a: 8'h01, b: 8'h02};
    parr[1] = '{a: 8'h03, b: 8'h04};
    if (parr == '{'{a: 8'h01, b: 8'h02}, '{a: 8'h03, b: 8'h04}}) begin
      // expected
    end
    else begin
      $display("FAIL: array of structs == nested pattern");
      $stop;
    end

    // -------------------------------------------------------
    // 10. Different element widths
    // -------------------------------------------------------
    wide_arr = '{32'hDEAD_BEEF, 32'hCAFE_BABE, 32'h1234_5678};
    if (wide_arr == '{32'hDEAD_BEEF, 32'hCAFE_BABE, 32'h1234_5678}) begin
      // expected
    end
    else begin
      $display("FAIL: wide array == pattern");
      $stop;
    end

    byte_arr = '{8'hAB, 8'hCD};
    if (byte_arr == '{8'hAB, 8'hCD}) begin
      // expected
    end
    else begin
      $display("FAIL: byte array == pattern");
      $stop;
    end

    // -------------------------------------------------------
    // 11. Negative case: pattern that should not match
    // -------------------------------------------------------
    if (arr4 == '{99, 99, 99, 99}) begin
      $display("FAIL: arr4 should not match all-99 pattern");
      $stop;
    end

    // -------------------------------------------------------
    // 12. Both sides are typed assignment patterns
    // -------------------------------------------------------
    if (arr4_t'{10, 20, 30, 40} == arr4_t'{10, 20, 30, 40}) begin
      // expected
    end
    else begin
      $display("FAIL: typed pattern == typed pattern");
      $stop;
    end

    if (arr4_t'{10, 20, 30, 40} != arr4_t'{10, 20, 30, 99}) begin
      // expected
    end
    else begin
      $display("FAIL: typed pattern != typed pattern");
      $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
