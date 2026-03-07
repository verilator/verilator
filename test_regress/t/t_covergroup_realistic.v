// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Realistic example: Bus transaction coverage

// verilog_format: off
`define stop $stop
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (/*AUTOARG*/);
  /* verilator lint_off UNSIGNED */
  logic [31:0] addr;
  logic [1:0]  burst_type;
  logic        valid;

  // Coverage for a memory bus interface
  covergroup bus_cg;
    // Address coverage with interesting regions
    coverpoint addr {
      bins zero_page   = {[32'h0000_0000:32'h0000_00FF]};
      bins boot_rom    = {[32'h0000_1000:32'h0000_1FFF]};
      bins dram        = {[32'h4000_0000:32'h7FFF_FFFF]};
      bins peripherals = {[32'h8000_0000:32'h9FFF_FFFF]};
    }

    // Burst type coverage (only when valid)
    coverpoint burst_type iff (valid) {
      bins single      = {2'b00};
      bins incr        = {2'b01};
      bins wrap        = {2'b10};
      bins reserved    = {2'b11};
    }
  endgroup

  bus_cg cg_inst;

  initial begin
    cg_inst = new;

    // Test various transactions

    // Boot sequence - should hit zero_page and boot_rom
    valid = 1;
    addr = 32'h0000_0010; burst_type = 2'b00; cg_inst.sample();
    addr = 32'h0000_1100; burst_type = 2'b01; cg_inst.sample();

    // After boot
    `checkr(cg_inst.get_inst_coverage(), 50.0);

    // DRAM access with wrap burst
    addr = 32'h4000_0000; burst_type = 2'b10; cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 75.0);

    // Peripheral access completes all addr bins
    addr = 32'h8000_0100; burst_type = 2'b11; cg_inst.sample();
    `checkr(cg_inst.get_inst_coverage(), 100.0);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
