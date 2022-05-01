// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2012 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// bug598

module t (/*AUTOARG*/
   // Outputs
   val,
   // Inputs
   clk
   );

   input           clk;
   output integer  val;
   integer         dbg_addr = 0;

   function func1;
      input en;
      input [31:0] a;
      func1 = en && (a == 1);
   endfunction

   function func2;
      input        en;
      input [31:0] a;
      func2 = en && (a == 2);
   endfunction

   always @(posedge clk) begin
      case( 1'b1 )
        // This line is OK:
        func1(1'b1, dbg_addr) : val = 1;
        // This fails:
        // %Error: Internal Error: test.v:23: ../V3Task.cpp:993: Function not underneath a statement
        func2(1'b1, dbg_addr) : val = 2;
        default : val = 0;
      endcase
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
