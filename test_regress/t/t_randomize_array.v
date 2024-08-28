// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class unconstrained_packed_array_test;

    rand bit [3:0] [2:0] [15:0] packed_array;

endclass

class unconstrained_unpacked_array_test;

  rand bit [2:0] [15:0] unpacked_array [3][5];
  
endclass

module t_randomize_array;
  
  unconstrained_packed_array_test  packed_class;
  unconstrained_unpacked_array_test unpacked_class;

  initial begin
    
    // Test 1: Packed Array Unconstrained Constrained Test
    packed_class = new();
    $display("\n--- Test 1: Packed Array Unconstrained Constrained Test ---");
    repeat(2) begin
      int success;
      success = packed_class.randomize();
      if (success != 1) $stop;
      $display("Packed array values:");
      for (int i = 0; i < 4; i++) begin
        $display("packed_array[%0d] = %0h", i, packed_class.packed_array[i]);
      end
      for (int i = 0; i < 4; i++) begin
        for (int j = 0; j < 3; j++) begin
          $display("packed_array[%0d][%0d] = %0h", i, j, packed_class.packed_array[i][j]);
        end
      end
      $display("---    ---    ---    ---    ---    ---");
    end

    // Test 2: Unpacked Array Unconstrained Constrained Test
    unpacked_class = new();
    $display("\n--- Test 2: Unpacked Array Unconstrained Constrained Test ---");
    repeat(2) begin
      int success;
      success = unpacked_class.randomize();
      if (success != 1) $stop;
      $display("Unpacked array values:");
      foreach (unpacked_class.unpacked_array[i]) 
        foreach (unpacked_class.unpacked_array[i][j]) begin
          $display("unpacked_array[%0d][%0d] = %0h", i, j, unpacked_class.unpacked_array[i][j]);
        end
      $display("---    ---    ---    ---    ---    ---");
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
