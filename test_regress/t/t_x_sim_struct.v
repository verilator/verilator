// DESCRIPTION: Verilator: Test X/Z four-state simulation with structs
//
// This test verifies four-state simulation with struct members.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

  // Struct with four-state members
  typedef struct packed {
    logic [3:0] a;
    logic [7:0] b;
    logic       flag;
  } my_struct_t;

  // Struct signals
  my_struct_t s1 = 16'hABCD;
  my_struct_t s2 = 16'h1234;
  my_struct_t sx;  // Uninitialized - should be X with --x-sim
  my_struct_t s_result;

  // Struct with X/Z values
  my_struct_t sx_val;
  initial begin
    sx_val.a = 4'bX101;
    sx_val.b = 8'bZ0101010;
    sx_val.flag = 1'bX;
  end

  // Mixed struct operations
  my_struct_t s_and;
  my_struct_t s_or;
  my_struct_t s_add;

  initial begin
    // Operations on struct members
    s_and = sx & sx_val;  // Uninitialized X & X = X
    s_or = s1 | sx_val;   // Normal | X = X
    s_add = s1 + sx;      // Normal + X = X

    $write("=== Struct Four-State Tests ===\n");

    $write("s1 = %b (initialized)\n", s1);
    $write("s2 = %b (initialized)\n", s2);
    $write("sx (uninitialized) = %b (expect X)\n", sx);

    $write("\n=== Struct with X/Z values ===\n");
    $write("sx_val.a = %b (X101)\n", sx_val.a);
    $write("sx_val.b = %b (Z0101010)\n", sx_val.b);
    $write("sx_val.flag = %b (X)\n", sx_val.flag);
    $write("sx_val = %b\n", sx_val);

    $write("\n=== Struct Operations ===\n");
    $write("sx & sx_val = %b (expect all X)\n", s_and);
    $write("s1 | sx_val = %b (expect X in members with X)\n", s_or);
    $write("s1 + sx = %b (expect all X)\n", s_add);

    // Test struct member access
    $write("\n=== Struct Member Access ===\n");
    $write("sx.a = %b (uninitialized member)\n", sx.a);
    $write("sx.b = %b (uninitialized member)\n", sx.b);
    $write("sx.flag = %b (uninitialized member)\n", sx.flag);

    // Test assignment to struct with X
    sx = sx_val;
    $write("\n=== After Assignment ===\n");
    $write("sx = %b (after sx = sx_val)\n", sx);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
