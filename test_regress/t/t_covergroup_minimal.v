// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Minimal test for covergroup parsing and code generation

module t;
   int unsigned addr;  // Use unsigned to avoid comparison warnings

   covergroup cg;
      cp_addr: coverpoint addr {
         bins low = {[0:127]};
         bins high = {[128:255]};
      }
   endgroup

   initial begin
      cg cg_inst;
      cg_inst = new;

      // Sample some values
      addr = 10;
      cg_inst.sample();

      addr = 200;
      cg_inst.sample();

      $display("Coverage: %0.1f%%", cg_inst.get_coverage());
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
