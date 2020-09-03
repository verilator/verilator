// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg [2:0] in;


   wire a,y,y_fixed;
   wire b = in[0];
   wire en = in[1];


   pullup(a);

   ChildA childa ( .A(a), .B(b), .en(en), .Y(y),.Yfix(y_fixed) );

   initial in=0;

   // Test loop
   always @ (posedge clk) begin


      in <= in + 1;

      $display ( "a %d b %d en %d y %d yfix: %d)" , a, b, en, y, y_fixed);
      if (en) begin
        // driving b
        // a should be b
        // y and yfix should also be b
        if (a!=b || y != b || y_fixed != b) begin
            $display ( "Expected a %d y %b yfix %b" , a, y, y_fixed);
            $stop;
        end

      end else begin
        // not driving b
        // a should be 1 (pullup)
        // y and yfix shold be 1
        if (a!=1 || y != 1 || y_fixed != 1) begin
            $display( "Expected a,y,yfix == 1");
            $stop;
        end
      end

      if (in==3) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module ChildA(inout A, input B, input en, output Y, output Yfix);

   // workaround
   wire a_in = A;

   ChildB childB(.A(A), .Y(Y));
   assign A = en ? B : 1'bz;


   ChildB childBfix(.A(a_in),.Y(Yfix));


endmodule

module ChildB(input A, output Y);
  assign Y = A;
endmodule
