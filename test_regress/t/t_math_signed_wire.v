// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Wilson Snyder.

// bug511
module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire [7:0] au;
   wire [7:0] as;

   Test1 test1 (.au);
   Test2 test2 (.as);

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] result=%x %x\n",$time, au, as);
`endif
      if (au != 'h12) $stop;
      if (as != 'h02) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

module Test1 (output [7:0] au);
   wire [7:0] 		b;
   wire signed [3:0] 	c;

   // verilator lint_off WIDTH
   assign c=-1;  // 'hf
   assign b=3;   // 'h3
   assign au=b+c; // 'h12
   // verilator lint_on WIDTH
endmodule


module Test2 (output [7:0] as);
   wire signed [7:0] 	b;
   wire signed [3:0] 	c;

   // verilator lint_off WIDTH
   assign c=-1;  // 'hf
   assign b=3;   // 'h3
   assign as=b+c; // 'h12
   // verilator lint_on WIDTH
endmodule
