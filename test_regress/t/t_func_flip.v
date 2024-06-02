// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define INT_RANGE     31:0
`define INT_RANGE     31:0      // Duplicate identical defs are OK
`define INT_RANGE_MAX 31
`define VECTOR_RANGE 511:0

module t (clk);

   // verilator lint_off WIDTH

   parameter WIDTH      = 16;       // Must be a power of 2
   parameter WIDTH_LOG2 = 4;        //          set to log2(WIDTH)
   parameter USE_BS     = 1;        // set to 1 for enable

   input      clk;

   function [`VECTOR_RANGE] func_tree_left;
      input [`VECTOR_RANGE]   x;          // x[width-1:0] is the input vector
      reg [`VECTOR_RANGE]     flip;
      begin
         flip = 'd0;
         func_tree_left = flip;
      end
   endfunction

   reg [WIDTH-1:0]     a;                      // value to be shifted
   reg [WIDTH-1:0]      tree_left;
   always @(a) begin : barrel_shift
      tree_left =  func_tree_left  (a);
   end  // barrel_shift

   integer cyc; initial cyc=1;
   always @ (posedge clk) begin
      if (cyc!=0) begin
         cyc <= cyc + 1;
         if (cyc==1) begin
            a = 5;
         end
         if (cyc==2) begin
            $display ("%x\n",tree_left);
            //if (tree_left != 'd15) $stop;
            $write("*-* All Finished *-*\n");
            $finish;
         end
      end
   end


endmodule
