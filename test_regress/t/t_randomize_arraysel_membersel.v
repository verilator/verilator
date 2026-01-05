// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class inner_class;
  logic [3:0] c;
  logic [3:0] d [2];
endclass

class test_class;
  logic [3:0] member[5];
  logic [3:0] member_2d[3][4];
  inner_class b;
endclass

module t;
  initial begin
    test_class example;
    example   = new;
    example.b = new;

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

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
