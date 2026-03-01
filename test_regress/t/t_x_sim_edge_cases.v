// Test file for X/Z four-state simulation edge cases
// This tests nested operations, mixed bit widths, arrays, and complex expressions

module t_x_sim_edge_cases;

  // Test signals with various bit widths
  wire [3:0]  a4 = 4'b1010;
  wire [7:0]  b8 = 8'b11001100;
  wire [15:0] c16 = 16'hABCD;
  
  // Four-state signals with X and Z values
  reg [3:0]  a4_4state = 4'b1010;
  reg [7:0]  b8_4state = 8'b11001100;
  reg [15:0] c16_4state = 16'hABCD;
  
  // Initialize with X and Z values
  initial begin
    a4_4state[0] = 1'bX;  // First bit is X
    b8_4state[4] = 1'bZ;  // Middle bit is Z
    c16_4state[7:4] = 4'bXZ10;  // Mixed X/Z in middle
  end

  // Four-state signals with X/Z
  reg [3:0]  x4 = 4'bX1X0;
  reg [7:0]  z8 = 8'bZZZZ1010;
  reg [15:0] xz16 = 16'hXZ10_XZ10_XZ10_XZ10;
  
  // Results for nested operations
  wire [3:0]  res1;
  wire [7:0]  res2;
  wire [15:0] res3;
  
  // Nested operations with X/Z propagation
  assign res1 = (a4_4state & x4) | (b8_4state ^ z8);
  assign res2 = (c16_4state + xz16) - (a4_4state * z8);
  assign res3 = (res1 << 2) | (res2 >> 4);

  // Mixed bit width operations
  wire [7:0]  mixed1;
  wire [15:0] mixed2;
  
  assign mixed1 = {a4_4state, b8_4state[3:0]};  // 4-bit + 4-bit = 8-bit
  assign mixed2 = {b8_4state, c16_4state[7:0]};  // 8-bit + 8-bit = 16-bit

  // Array of four-state signals
  reg [3:0] array4state [0:3];
  
  initial begin
    array4state[0] = 4'b1010;  // Deterministic
    array4state[1] = 4'bX1X0;  // Has X
    array4state[2] = 4'bZ0Z1;  // Has Z
    array4state[3] = 4'bXZ10;  // Mixed X/Z
  end

  // Operations on array elements
  wire [3:0] array_res1;
  wire [3:0] array_res2;
  
  assign array_res1 = array4state[0] & array4state[1];  // Deterministic & X
  assign array_res2 = array4state[2] | array4state[3];  // Z & Mixed X/Z

  // Complex expressions with multiple X/Z
  wire [7:0] complex1;
  wire [15:0] complex2;
  
  assign complex1 = (a4_4state + x4) * (b8_4state - z8);
  assign complex2 = ((c16_4state ^ xz16) + 16'hFFFF) & mixed2;

  // Test $display with four-state signals
  initial begin
    $display("=== Edge Case Tests ===");
    $display("a4_4state (4-bit with X): %b", a4_4state);
    $display("b8_4state (8-bit with Z): %b", b8_4state);
    $display("c16_4state (16-bit with X/Z): %b", c16_4state);
    $display("x4 (X values): %b", x4);
    $display("z8 (Z values): %b", z8);
    $display("xz16 (mixed X/Z): %b", xz16);
    
    $display("\n=== Nested Operations ===");
    $display("res1 = (a4_4state & x4) | (b8_4state ^ z8): %b", res1);
    $display("res2 = (c16_4state + xz16) - (a4_4state * z8): %b", res2);
    $display("res3 = (res1 << 2) | (res2 >> 4): %b", res3);
    
    $display("\n=== Mixed Bit Width Operations ===");
    $display("mixed1 = {a4_4state, b8_4state[3:0]}: %b", mixed1);
    $display("mixed2 = {b8_4state, c16_4state[7:0]}: %b", mixed2);
    
    $display("\n=== Array Operations ===");
    $display("array_res1 = array4state[0] & array4state[1]: %b", array_res1);
    $display("array_res2 = array4state[2] | array4state[3]: %b", array_res2);
    
    $display("\n=== Complex Expressions ===");
    $display("complex1 = (a4_4state + x4) * (b8_4state - z8): %b", complex1);
    $display("complex2 = ((c16_4state ^ xz16) + 16'hFFFF) & mixed2: %b", complex2);
    
    #10 $finish;
  end

endmodule