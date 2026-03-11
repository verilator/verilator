// Test Z display - very simple

module t;
  reg [7:0] z8 = 8'bZZZZ1010;
  
  initial begin
    $display("z8=%b", z8);
    $finish;
  end
endmodule
