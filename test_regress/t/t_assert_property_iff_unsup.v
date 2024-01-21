module test(
  input clk,
  input rst,
  input x
);

a: assert property (disable iff(rst !== 1'b0) @(posedge clk) !x);

endmodule
