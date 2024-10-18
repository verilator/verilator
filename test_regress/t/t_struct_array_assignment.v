// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by PlanV GmbH.
// SPDX-License-Identifier: CC0-1.0

class unconstrained_struct_array_test;

  typedef struct {
    rand int field_a;
    rand int field_b;
    rand int field_c;
  } simple_struct_t;

  rand simple_struct_t struct_array[3]; // Unpacked array

  function new();
    // Initialize struct_array
    struct_array = '{'{default: 0}, '{default: 1}, '{default: 2}};
  endfunction

  // Self-check function to validate the array contents
  function void self_test();
    foreach (struct_array[i]) begin
      if (struct_array[i].field_a != i) $stop;
      if (struct_array[i].field_b != i + 1) $stop;
      if (struct_array[i].field_c != i + 2) $stop;
    end
  endfunction

endclass

module t_struct_array_assignment;
  unconstrained_struct_array_test  cl;

  initial begin

    cl = new();

    foreach(cl.struct_array[i]) begin
      cl.struct_array[i].field_a = i;
      cl.struct_array[i].field_b = i + 1;
      cl.struct_array[i].field_c = i + 2;
    end

    cl.self_test();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
