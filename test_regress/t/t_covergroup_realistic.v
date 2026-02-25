// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Matthew Ballance
// SPDX-License-Identifier: CC0-1.0

// Realistic example: Bus transaction coverage

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
        check_coverage(50.0, "after boot");

        // DRAM access with wrap burst
        addr = 32'h4000_0000; burst_type = 2'b10; cg_inst.sample();
        check_coverage(75.0, "after dram access");

        // Peripheral access completes all addr bins
        addr = 32'h8000_0100; burst_type = 2'b11; cg_inst.sample();
        check_coverage(100.0, "complete");

        $write("*-* All Finished *-*\n");
        $finish;
    end

    task check_coverage(real expected, string label);
        real cov;
        cov = cg_inst.get_inst_coverage();
        $display("Bus Coverage %s: %0.2f%% (expected ~%0.2f%%)", label, cov, expected);
        if (cov < expected - 1.0 || cov > expected + 1.0) begin
            $error("Coverage mismatch: got %0.2f%%, expected ~%0.2f%%", cov, expected);
            $stop;
        end
    endtask
endmodule
