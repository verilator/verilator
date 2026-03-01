// DESCRIPTION: Verilator: Test X/Z four-state simulation with --x-sim
//
// SPDX-FileCopyrightText: 2026
// SPDX-License-Identifier: LGPL-3.0-only

module t;
  reg [3:0] a = 4'bXXXX;
  reg [3:0] b = 4'b1010;
  reg [3:0] y_and;
  
  initial begin
    y_and = a & b;
    
    $display("a = %b", a);
    $display("b = %b", b);
    $display("a & b = %b", y_and);
    $finish;
  end
endmodule
