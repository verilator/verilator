// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

class Cls;
   int q[$];
   function new();
      q.push_back(1);
      q.push_back(2);
      q.push_back(3);
   endfunction
endclass

module t (/*AUTOARG*/);

   int two[5:6];

   if (1) begin : named
      Cls c;
   end

   function [63:0] crc(input [63:0] sum, input [31:0] a, input [31:0] b, input [31:0] c, input [31:0] d);
      crc = {sum[62:0],sum[63]} ^ {20'b0,a[7:0], 4'h0,b[7:0], 4'h0,c[7:0], 4'h0,d[7:0]};
   endfunction

   bit [63:0] sum;

   initial begin
      named.c = new;
      sum = 0;
      foreach (named.c.q[i]) begin
         foreach (two[j]) begin
            // $display(i, j);
            sum = crc(sum, i, named.c.q[i], j, 0);
         end
      end
      `checkh(sum, 64'h000000a02d0fc000);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
