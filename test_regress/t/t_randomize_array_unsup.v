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

class unconstrained_struct_array_test;

  typedef struct {
    rand int field_a;
    rand int field_b;
  } simple_struct_t;

  rand simple_struct_t struct_array[3];

  function new();
    struct_array = '{'{default: 0}, '{default: 1}, '{default: 2}};
  endfunction

  function void check_randomization();
    foreach (struct_array[i]) begin
      `check_rand(this, struct_array[i].field_a)
      `check_rand(this, struct_array[i].field_b)
    end
  endfunction

endclass

module t_randomize_array_unsup;

    unconstrained_struct_array_test struct_array_class;

    initial begin

        // Test: Struct Array Unconstrained Constrained Test
        struct_array_class = new();
        repeat(2) begin
        struct_array_class.check_randomization();
        end

        $write("*-* All Finished *-*\n");
        $finish;
    end

endmodule
