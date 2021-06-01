// DESCRIPTION: Verilator: Verilog Test module for Issue#2938
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Julien Margetts (Originally provided by YanJiun)

module test (
  input      [2:0] a,
  input      [3:0] c,

  output reg [7:0] b
);

  integer i;

  always @ (*)
  begin
    case(a)
      {3'b000}: b = 8'd1;
      {3'b001}:
        for(i=0;i<4;i=i+1) b[i*2+:2] = 2'(c[i]);
      {3'b010}: b = 8'd3;
      {3'b011}: b = 8'd4;
      default : b = 0;
    endcase
  end

endmodule
