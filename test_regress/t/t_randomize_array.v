// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

`define check_rand(cl, field) \
begin \
   longint prev_result; \
   int ok = 0; \
   for (int i = 0; i < 10; i++) begin \
      longint result; \
      void'(cl.randomize()); \
      result = longint'(field); \
      if (i > 0 && result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) $stop; \
end

class unconstrained_packed_array_test;

    rand bit [3:0] [2:0] [15:0] packed_array;
    function new();
      packed_array = '{default: '{default: '{default: 'h0}}};
    endfunction

    function void check_randomization();
      `check_rand(this, this.packed_array)
    endfunction

endclass

class unconstrained_unpacked_array_test;

  rand bit [2:0] [15:0] unpacked_array [3][5];
  function new();
    unpacked_array = '{ '{default: '{default: 'h0}},
                        '{default: '{default: 'h1}},
                        '{default: '{default: 'h2}}};
  endfunction

  function void check_randomization();
    foreach (unpacked_array[i]) begin
      foreach (unpacked_array[i][j]) begin
        // At the innermost packed level, invoke check_rand
        `check_rand(this, this.unpacked_array[i][j])
      end
    end
  endfunction

endclass

class unconstrained_dynamic_array_test;

  rand int dynamic_array_1d[];
  rand int dynamic_array_2d[][];

  function new();
    // Initialize 1D dynamic array
    dynamic_array_1d = new[5];
    foreach(dynamic_array_1d[i]) begin
      dynamic_array_1d[i] = 'h0 + i;
    end

    // Initialize 2D dynamic array
    dynamic_array_2d = new[3];
    foreach(dynamic_array_2d[i]) begin
      dynamic_array_2d[i] = new[3];
      foreach(dynamic_array_2d[i][j]) begin
        dynamic_array_2d[i][j] = 'h0 + i + j;
      end
    end
  endfunction

  function void check_randomization();
    foreach (dynamic_array_1d[i]) begin
      `check_rand(this, dynamic_array_1d[i])
    end
    foreach (dynamic_array_2d[i]) begin
      foreach (dynamic_array_2d[i][j]) begin
        `check_rand(this, dynamic_array_2d[i][j])
      end
    end
  endfunction

endclass

module t_randomize_array;
  unconstrained_packed_array_test  packed_class;
  unconstrained_unpacked_array_test unpacked_class;
  unconstrained_dynamic_array_test dynamic_class;

  initial begin
    // Test 1: Packed Array Unconstrained Constrained Test
    packed_class = new();
    repeat(2) begin
      packed_class.check_randomization();
    end

    // Test 2: Unpacked Array Unconstrained Constrained Test
    unpacked_class = new();
    repeat(2) begin
      unpacked_class.check_randomization();
    end

    dynamic_class = new();
    repeat(2) begin
      dynamic_class.check_randomization();
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
