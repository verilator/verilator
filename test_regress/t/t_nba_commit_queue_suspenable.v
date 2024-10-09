// DESCRIPTION: Verilator: Test of select from constant
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t;

   reg clk = 0;

   always #50 clk = ~clk;

   initial begin
     #1000;
     $write("*-* All Finished *-*\n");
     $finish;
   end

   int cyc = 0;
   always @(posedge clk) cyc <= cyc + 1;

   localparam SIZE = 65536;

   // Case 1: Array NBA inside suspendable
   int array1 [SIZE];
   always @ (posedge clk) begin
      #1;
      for (int i=0; i<SIZE; i++) array1[i] <= cyc + i;
      if (cyc > 1) begin
        for (int i=0; i<SIZE; i++) `checkh(array1[i], cyc - 1 + i);
      end
      #1;
      for (int i=0; i<SIZE; i++) `checkh(array1[i], cyc + i);
   end

   // Case 2: Array NBA to array also assigned in suspendable
   int array2 [SIZE];
   always @ (posedge clk) begin
      for (int i=0; i<SIZE; i++) array2[i] <= cyc + i;
   end

   always @(posedge clk) begin
      #2 array2[1] <= 1111;
      #2 array2[3] <= 3333;
      #2 array2[5] <= 5555;
   end

   initial begin
      @(posedge clk);
      @(posedge clk);
      @(posedge clk);
      #1;
      for (int i=0; i<SIZE; i++) `checkh(array2[i], cyc - 1 + i);
      #2;
      for (int i=0; i<SIZE; i++) `checkh(array2[i], i == 1 ? 1111 : cyc - 1 + i);
      #2;
      for (int i=0; i<SIZE; i++) `checkh(array2[i], i == 1 ? 1111 : i == 3 ? 3333 : cyc - 1 + i);
      #2;
      for (int i=0; i<SIZE; i++) `checkh(array2[i], i == 1 ? 1111 : i == 3 ? 3333 : i == 5 ? 5555 : cyc - 1 + i);
   end


endmodule
