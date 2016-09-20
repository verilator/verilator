// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2016 by Wilson Snyder.

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/);

   // verilator lint_off LITENDIAN
   // verilator lint_off WIDTH

   reg [63:0] sum;
   reg [2:1] [4:3] array [5:6] [7:8];
   reg [1:2] [3:4] larray [6:5] [8:7];

   function [63:0] crc (input [63:0] sum, input [31:0] a, input [31:0] b, input [31:0] c, input [31:0] d);
      crc = {sum[62:0],sum[63]} ^ {4'b0,a[7:0], 4'h0,b[7:0], 4'h0,c[7:0], 4'h0,d[7:0]};
   endfunction

   initial begin
      sum = 0;
      foreach (array[a]) begin
	 sum = crc(sum, a, 0, 0, 0);
      end
      `checkh(sum, 64'h000000c000000000);

      sum = 0;
      foreach (array[a,b]) begin
	 sum = crc(sum, a, b, 0, 0);
      end
      `checkh(sum, 64'h000003601e000000);

      sum = 0;
      foreach (array[a,b,c]) begin
	 sum = crc(sum, a, b, c, 0);
      end
      `checkh(sum, 64'h00003123fc101000);

      sum = 0;
      foreach (array[a,b,c,d]) begin
	 sum = crc(sum, a, b, c, d);
      end
      `checkh(sum, 64'h0030128ab2a8e557);

      //

      sum = 0;
      foreach (larray[a]) begin
	 sum = crc(sum, a, 0, 0, 0);
      end
      `checkh(sum, 64'h0000009000000000);

      sum = 0;
      foreach (larray[a,b]) begin
	 sum = crc(sum, a, b, 0, 0);
	 sum = sum + {4'b0,a[7:0], 4'h0,b[7:0]};
      end
      `checkh(sum, 64'h000002704b057073);

      sum = 0;
      foreach (larray[a,b,c]) begin
	 sum = crc(sum, a, b, c, 0);
      end
      `checkh(sum, 64'h00002136f9000000);

      sum = 0;
      foreach (larray[a,b,c,d]) begin
	 sum = crc(sum, a, b, c, d);
      end
      `checkh(sum, 64'h0020179aa7aa0aaa);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
