// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Test 3-way cross coverage

module t;
   logic [1:0] addr;
   logic cmd;
   logic mode;

   // Covergroup with 3-way cross coverage
   covergroup cg;
      cp_addr: coverpoint addr {
         bins addr0 = {0};
         bins addr1 = {1};
         bins addr2 = {2};
      }
      cp_cmd: coverpoint cmd {
         bins read = {0};
         bins write = {1};
      }
      cp_mode: coverpoint mode {
         bins normal = {0};
         bins debug = {1};
      }
      // 3-way cross: addr x cmd x mode = 3 x 2 x 2 = 12 cross bins
      addr_cmd_mode: cross cp_addr, cp_cmd, cp_mode;
   endgroup

   cg cg_inst = new;

   initial begin
      // Hit different 3-way cross bins
      addr = 0; cmd = 0; mode = 0; cg_inst.sample(); // addr0 x read x normal
      $display("Sample 1: addr=%0d, cmd=%0d, mode=%0d", addr, cmd, mode);

      addr = 1; cmd = 1; mode = 0; cg_inst.sample(); // addr1 x write x normal
      $display("Sample 2: addr=%0d, cmd=%0d, mode=%0d", addr, cmd, mode);

      addr = 2; cmd = 0; mode = 1; cg_inst.sample(); // addr2 x read x debug
      $display("Sample 3: addr=%0d, cmd=%0d, mode=%0d", addr, cmd, mode);

      addr = 0; cmd = 1; mode = 1; cg_inst.sample(); // addr0 x write x debug
      $display("Sample 4: addr=%0d, cmd=%0d, mode=%0d", addr, cmd, mode);

      addr = 1; cmd = 0; mode = 1; cg_inst.sample(); // addr1 x read x debug
      $display("Sample 5: addr=%0d, cmd=%0d, mode=%0d", addr, cmd, mode);

      // Check coverage
      // Total bins:
      // - 3 bins in cp_addr (addr0, addr1, addr2)
      // - 2 bins in cp_cmd (read, write)
      // - 2 bins in cp_mode (normal, debug)
      // - 12 bins in 3-way cross (3 x 2 x 2)
      // Total = 19 bins
      // Hit: addr0, addr1, addr2 (3), read, write (2), normal, debug (2), 5 cross bins
      // Total = 12 out of 19 = 63.2%
      $display("Coverage: %0.1f%%", cg_inst.get_inst_coverage());

      if (cg_inst.get_inst_coverage() < 62.0 || cg_inst.get_inst_coverage() > 64.0) begin
         $display("%%Error: Expected coverage around 63%%, got %0.1f%%",
                  cg_inst.get_inst_coverage());
         $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
