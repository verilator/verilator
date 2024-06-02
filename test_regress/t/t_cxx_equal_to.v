// DESCRIPTION: Verilator: Verilog Test module
//
// On some platforms (i.e. FreeBSD 12) this triggered:
//
//   Active region did not converge.
//
// due to the mistaken belief that the AstVarScope node for TOP->t__DOT__clk
// is equal to the AstVarScope node for TOP->t__DOT__rst.  This occured because
// AstVarScope was missing an appropriate same method and is tickled by the LLVM
// libcxx library.
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by John Wehle.
// SPDX-License-Identifier: CC0-1.0

module t;

  wire [1:0] out;
  reg        in;
  reg        rst;
  reg        clk;

  initial begin
    clk = 0;
    rst = 0;

    #10 rst = 1;
    #10 rst = 0;

    in = 1'b0;

    #30 $write("*-* All Finished *-*\n");
    $finish;
  end

  always begin
    #10 clk <= !clk;
  end

  Test test(.out(out), .in(in),
	    .clk(clk), .rst(rst));
endmodule


module Test(/*AUTOARG*/
   // Outputs
   out,
   // Inputs
   clk, in, rst
   );

   input             clk;
   input             in;
   input             rst;
   output wire [1:0] out;

   reg [1:0] s;
   reg       sin;

   assign out = s;

   always @(posedge clk)
     begin
       s[1] <= in;
       s[0] <= sin;
     end

   always @(negedge clk, posedge rst)
     if (rst)
       sin <= 1'b0;
     else
       sin <= in;

endmodule
