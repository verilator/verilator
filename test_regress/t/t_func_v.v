// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Chandan Egbert
// SPDX-License-Identifier: CC0-1.0

// See bug569

module t();
`ifdef T_FUNC_V_NOINL
   // verilator no_inline_module
`endif
   level1 ul1();
   initial ul1.doit(4'b0);
endmodule

module level1();
`ifdef T_FUNC_V_NOINL
   // verilator no_inline_module
`endif
   level2 ul2();

   task doit(input logic [3:0] v);
      ul2.mem = v;
      $write("*-* All Finished *-*\n");
      $finish;
   endtask
endmodule

module level2();
`ifdef T_FUNC_V_NOINL
   // verilator no_inline_module
`endif
   logic [3:0] mem;
endmodule
