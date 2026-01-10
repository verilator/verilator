// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef struct {int x;} struct_t;

class inner_class;
  logic [3:0] c;
  logic [3:0] d[2];
  logic [3:0] dyn[];
  struct_t s;
endclass

class test_class;
  logic [3:0] member[5];
  logic [3:0] member_2d[3][4];
  inner_class b;
endclass

module t;
  initial begin
    int x = 2;
    test_class example;
    example = new;
    example.b = new;
    example.b.dyn = new[3];

    // Simple array element access
    repeat (5) begin
      if (std::randomize(example.member[1]) with {example.member[1] inside {[0 : 3]};} == 0) $stop;
      if (example.member[1] > 3) $stop;
    end

    // Different array indices
    repeat (5) begin
      if (std::randomize(example.member[0]) with {example.member[0] inside {[5 : 7]};} == 0) $stop;
      if (example.member[0] < 5 || example.member[0] > 7) $stop;
    end

    // Last element
    repeat (5) begin
      if (std::randomize(example.member[4]) with {example.member[4] inside {[10 : 15]};} == 0)
        $stop;
      if (example.member[4] < 10 || example.member[4] > 15) $stop;
    end

    // 2D array access
    repeat (5) begin
      if (std::randomize(
              example.member_2d[1][2]
          ) with {
            example.member_2d[1][2] inside {[8 : 12]};
          } == 0)
        $stop;
      if (example.member_2d[1][2] < 8 || example.member_2d[1][2] > 12) $stop;
    end

    // 2D array different indices
    repeat (5) begin
      if (std::randomize(
              example.member_2d[0][0]
          ) with {
            example.member_2d[0][0] inside {[1 : 4]};
          } == 0)
        $stop;
      if (example.member_2d[0][0] < 1 || example.member_2d[0][0] > 4) $stop;
    end

    // Nested object: obj.b.c
    repeat (5) begin
      if (std::randomize(example.b.c) with {example.b.c inside {[5 : 9]};} == 0) $stop;
      if (example.b.c < 5 || example.b.c > 9) $stop;
    end

    // Nested object with array: obj.b.d[0]
    repeat (5) begin
      if (std::randomize(example.b.d[0]) with {example.b.d[0] inside {[11 : 14]};} == 0) $stop;
      if (example.b.d[0] < 11 || example.b.d[0] > 14) $stop;
    end

    // Nested object with array: obj.b.d[1] (different index)
    repeat (5) begin
      if (std::randomize(example.b.d[1]) with {example.b.d[1] inside {[2 : 6]};} == 0) $stop;
      if (example.b.d[1] < 2 || example.b.d[1] > 6) $stop;
    end

    // Nested object with dynamic array: obj.b.dyn[x]
    repeat (5) begin
      if (std::randomize(example.b.dyn[x]) with {example.b.dyn[x] inside {[1 : 3]};} == 0) $stop;
      if (example.b.dyn[x] < 1 || example.b.dyn[x] > 3) $stop;
    end

    // Nested object with struct: obj.b.s.x
    repeat (5) begin
      if (std::randomize(example.b.s.x) with {example.b.s.x inside {[7 : 9]};} == 0) $stop;
      if (example.b.s.x < 7 || example.b.s.x > 9) $stop;
    end

    // Inline randomization of object with array
    repeat (5) begin
      if (example.randomize(b) with {b.d[1] inside {[2 : 6]};} == 0) $stop;
      if (example.b.d[1] < 2 || example.b.d[1] > 6) $stop;
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
