// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Ethan Sifferman
// SPDX-License-Identifier: CC0-1.0

module module_with_struct;
  typedef struct {int field;} struct_t;
  struct_t struct_variable;
  initial begin
    struct_variable.field = 1;
    if (struct_variable.field != 1) $stop;
  end
endmodule

module module_not_inlined;
  /* verilator no_inline_module */
  module_with_struct wrapped_instance ();
endmodule

module t;
  module_with_struct direct_instance ();
  module_not_inlined indirect_instance ();
  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
