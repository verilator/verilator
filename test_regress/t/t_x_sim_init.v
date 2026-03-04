// DESCRIPTION: Verilator: Test X initialization with --x-sim
//
// This test verifies X initialization of four-state signals when --x-sim is enabled.
// Four-state signals should initialize to X at time 0.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t(input clk);

// Test that four-state signals initialize to X
logic [3:0] sig_4state;  // Should be X at init
logic        sig_bit;    // Single bit should be X at init

// Counter to wait for first clock
integer count = 0;

always @(posedge clk) begin
    count <= count + 1;

    if (count == 0) begin
        // First cycle - check initialization
        // sig_4state should be XXXX (all X)
        // sig_bit should be X
        $write("Cycle %0d: sig_4state = %b (expect xxxx)\n", count, sig_4state);
        $write("Cycle %0d: sig_bit = %b (expect x)\n", count, sig_bit);
    end
    else if (count == 1) begin
        // After first clock, values should be assigned
        $write("Cycle %0d: sig_4state = %b\n", count, sig_4state);
        $write("Cycle %0d: sig_bit = %b\n", count, sig_bit);
        $write("*-* All Finished *-*\n");
        $finish;
    end
end

endmodule
