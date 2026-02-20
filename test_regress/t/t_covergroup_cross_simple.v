// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test basic cross coverage with 2-way cross

module t;
   logic [1:0] addr;
   logic cmd;
   logic clk;

   // Covergroup with cross coverage
   covergroup cg;
      cp_addr: coverpoint addr {
         bins addr0 = {0};
         bins addr1 = {1};
         bins addr2 = {2};
         bins addr3 = {3};
      }
      cp_cmd: coverpoint cmd {
         bins read = {0};
         bins write = {1};
      }
      // Cross coverage: addr x cmd = 4 x 2 = 8 bins
      addr_cmd: cross cp_addr, cp_cmd;
   endgroup

   cg cg_inst = new;

   initial begin
      // Hit different cross bins
      addr = 0; cmd = 0; cg_inst.sample(); // addr0 x read
      $display("After sample 1: addr=%0d, cmd=%0d", addr, cmd);

      addr = 1; cmd = 1; cg_inst.sample(); // addr1 x write
      $display("After sample 2: addr=%0d, cmd=%0d", addr, cmd);

      addr = 2; cmd = 0; cg_inst.sample(); // addr2 x read
      $display("After sample 3: addr=%0d, cmd=%0d", addr, cmd);

      addr = 0; cmd = 1; cg_inst.sample(); // addr0 x write
      $display("After sample 4: addr=%0d, cmd=%0d", addr, cmd);

      // Check coverage - should be 50% (4 out of 8 bins hit)
      // Actually, with cross bins, we have:
      // - 4 bins in cp_addr: addr0, addr1, addr2, addr3
      // - 2 bins in cp_cmd: read, write
      // - 8 bins in cross (4 x 2)
      // Hit: addr0, addr1, addr2 (3 bins), read, write (2 bins), 4 cross bins
      // Total = 9 out of 14 = 64.3%
      $display("Coverage: %0.1f%%", cg_inst.get_inst_coverage());

      if (cg_inst.get_inst_coverage() < 63.0 || cg_inst.get_inst_coverage() > 65.0) begin
         $display("%%Error: Expected coverage around 64%%, got %0.1f%%",
                  cg_inst.get_inst_coverage());
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
