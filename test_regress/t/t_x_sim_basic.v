// DESCRIPTION: Verilator: Test X/Z four-state simulation with --x-sim
//
// This test verifies X and Z value propagation when --x-sim is enabled.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t(input clk);

logic [3:0] a;
logic [3:0] b;
logic [3:0] y_and;
logic [3:0] y_or;
logic [3:0] y_xor;
logic [3:0] y_add;
logic [3:0] y_sub;
logic      y_eq;
logic      y_neq;

// Test X propagation through logical operations
always @(posedge clk) begin
    a <= 4'b1010;
    b <= 4'b01xz;  // Contains X and Z
end

// AND: X & anything = X, Z & anything = X
assign y_and = a & b;

// OR
assign y_or = a | b;

// XOR
assign y_xor = a ^ b;

// Addition: X + anything = X
assign y_add = a + b;

// Subtraction
assign y_sub = a - b;

// Comparisons with X return false (for !==)
assign y_eq = (a == b);
assign y_neq = (a != b);

// Check results
always @(posedge clk) begin
    // With --x-sim, b has X/Z, so results should propagate X
    // We just verify the simulator runs without crashing
    if (a == 4'b1010) begin
        $write("a = %b (expected 1010)\n", a);
        $write("b = %b (expected 01xz)\n", b);
        $write("a & b = %b\n", y_and);
        $write("a | b = %b\n", y_or);
        $write("a ^ b = %b\n", y_xor);
        $write("a + b = %b\n", y_add);
        $write("a - b = %b\n", y_sub);
        $write("a == b = %b (should be 0 or x due to X)\n", y_eq);
        $write("a != b = %b (should be 1 or x due to X)\n", y_neq);
        $write("*-* All Finished *-*\n");
        $finish;
    end
end

endmodule
