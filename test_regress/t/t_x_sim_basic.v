// DESCRIPTION: Verilator: Test X/Z four-state simulation with --x-sim
//
// This test verifies four-state signal initialization when --x-sim is enabled.
// Uninitialized signals should be X, not 0.
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;

logic [3:0] a;  // Uninitialized - should be X with --x-sim
logic [3:0] b = 4'b1010;  // Initialized

logic [3:0] y_and;
logic [3:0] y_or;
logic [3:0] y_xor;
logic [3:0] y_add;
logic [3:0] y_sub;

initial begin
    // a is uninitialized - with --x-sim it should be X
    
    // Test operations with X
    // AND with all 1s: X & 1 = X
    y_and = a & b;
    
    // OR with all 0s: X | 0 = X  
    y_or = a | 4'b0000;
    
    // XOR with all 0s: X ^ 0 = X
    y_xor = a ^ 4'b0000;
    
    // Add: X + anything = X
    y_add = a + b;
    
    // Sub: X - anything = X
    y_sub = a - b;

    $write("Testing four-state simulation with --x-sim:\n");
    $write("b = %b (initialized to 1010)\n", b);
    $write("a (uninitialized) = %b (should be xxxx with --x-sim)\n", a);
    $write("a & b = %b (should be xxxx if a is X)\n", y_and);
    $write("a | 0000 = %b (should be xxxx if a is X)\n", y_or);
    $write("a ^ 0000 = %b (should be xxxx if a is X)\n", y_xor);
    $write("a + b = %b (should be xxxx if a is X)\n", y_add);
    $write("a - b = %b (should be xxxx if a is X)\n", y_sub);
    $write("*-* All Finished *-*\n");
    $finish;
end

endmodule
