// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Alex Solomatnikov.

//bug595

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   logic [6-1:0] foo; initial foo = 20;

   dut #(.W(6)) udut(.clk(clk),
                     .foo(foo-16));
endmodule

module dut
    #(parameter W = 1)
    (input logic clk,
     input logic [W-1:0] foo);

    genvar i;
    generate
       for (i = 0; i < W; i++) begin
          suba ua(.clk(clk), .foo(foo[i]));
       end
    endgenerate
endmodule

module suba
  (input logic clk,
   input logic foo);

   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
