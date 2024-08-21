// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);

   // verilator lint_off ASCRANGE
   // verilator lint_off WIDTH

   reg [63:0] sum;  // Checked not in objects
   reg [63:0] add;
   reg [2:1] [4:3] array [5:6] [7:8];
   reg [1:2] [3:4] larray [6:5] [8:7];
   bit [31:0]      depth1_array [0:0];
   int             oned [3:1];
   int             twod [3:1][9:8];

   typedef struct packed {
      reg [1:0] [63:0] subarray;
   } str_t;
   typedef struct packed {
      str_t mid;
   } mid_t;

   function [63:0] crc (input [63:0] sum, input [31:0] a, input [31:0] b, input [31:0] c, input [31:0] d);
      crc = {sum[62:0],sum[63]} ^ {4'b0,a[7:0], 4'h0,b[7:0], 4'h0,c[7:0], 4'h0,d[7:0]};
   endfunction

   function [63:0] test1;
      test1 = 0;
      // We use 'index_' as the prefix for all loop vars,
      // this allows t_foreach.pl to confirm that all loops
      // have been unrolled and flattened away and no loop vars
      // remain in the generated .cpp
      foreach (depth1_array[index_a]) begin
         test1 = crc(test1, index_a, 0, 0, 0);

         // Ensure the index never goes out of bounds.
         // We used to get this wrong for an array of depth 1.
         if (index_a == -1) return 7;
         if (index_a == 1) return 7;
      end
   endfunction
   localparam par1 = test1();

   function [63:0] test2;
      test2 = 0;
      foreach (array[index_a]) begin
         test2 = crc(test2, index_a, 0, 0, 0);
      end
   endfunction
   localparam par2 = test2();

   function [63:0] test3;
      test3 = 0;
      foreach (array[index_a,index_b]) begin
         test3 = crc(test3, index_a, index_b, 0, 0);
      end
   endfunction
   localparam par3 = test3();

   function [63:0] test4;
      test4 = 0;
      foreach (array[index_a,index_b,index_c]) begin
         test4 = crc(test4, index_a, index_b, index_c, 0);
      end
   endfunction
   localparam par4 = test4();

   function [63:0] test5;
      test5 = 0;
      foreach (array[index_a,index_b,index_c,index_d]) begin
         test5 = crc(test5, index_a, index_b, index_c, index_d);
      end
   endfunction
   localparam par5 = test5();

   function [63:0] test6;
      // comma syntax
      test6 = 0;
      foreach (array[,index_b]) begin
         $display(index_b);
         test6 = crc(test6, 0, index_b, 0, 0);
      end
   endfunction
   localparam par6 = test6();

   function [63:0] test7;
      test7 = 0;
      foreach (larray[index_a]) begin
         test7 = crc(test7, index_a, 0, 0, 0);
      end
   endfunction
   localparam par7 = test7();

   function [63:0] test8;
      test8 = 0;
      foreach (larray[index_a,index_b]) begin
         test8 = crc(test8, index_a, index_b, 0, 0);
         test8 = test8 + {4'b0,index_a[7:0], 4'h0,index_b[7:0]};
      end
   endfunction
   localparam par8 = test8();

   function [63:0] test9;
      test9 = 0;
      foreach (larray[index_a,index_b,index_c]) begin
         test9 = crc(test9, index_a, index_b, index_c, 0);
      end
   endfunction
   localparam par9 = test9();

   function [63:0] test10;
      test10 = 0;
      foreach (larray[index_a,index_b,index_c,index_d]) begin
         test10 = crc(test10, index_a, index_b, index_c, index_d);
      end
   endfunction
   localparam par10 = test10();

   function [63:0] test11;
      automatic mid_t strarray[3];
      strarray = '{
         '{ '{ '{2, 1} } },
         '{ '{ '{5, 4} } },
         '{ '{ '{7, 6} } }
      };
      test11 = 0;
      foreach (strarray[s])
        foreach (strarray[s].mid.subarray[ss])
          test11 += strarray[s].mid.subarray[ss];
   endfunction
   localparam par11 = test11();

   function [63:0] test12;
      test12 = 0;
      foreach (oned[i]) begin
         ++test12;
         break;
      end
   endfunction
   localparam par12 = test12();

   function [63:0] test13;
      test13 = 0;
      foreach (oned[i]) begin
         ++test13;
         continue;
         test13 += 100;
      end
   endfunction
   localparam par13 = test13();

   function [63:0] test14;
      test14 = 0;
      foreach (twod[i, j]) begin
         ++test14;
         break;
      end
   endfunction
   localparam par14 = test14();

   function [63:0] test15;
      test15 = 0;
      foreach (twod[i, j]) begin
         ++test15;
         continue;
         test15 += 100;
      end

      foreach (twod[i, j]);  // Null body check
   endfunction
   localparam par15 = test15();

   function automatic [63:0] test16;
      string str1 = "";
      test16 = 0;
      foreach(str1[i]) begin
         test16++;
      end
   endfunction
   localparam par16 = test16();

   initial begin
      `checkh(par1, 64'h0);
      `checkh(par2, 64'h000000c000000000);
      `checkh(par3, 64'h000003601e000000);
      `checkh(par4, 64'h00003123fc101000);
      `checkh(par5, 64'h0030128ab2a8e557);
      `checkh(par6, 64'h0000000006000000);
      `checkh(par7, 64'h0000009000000000);
      `checkh(par8, 64'h000002704b057073);
      `checkh(par9, 64'h00002136f9000000);
      `checkh(par10, 64'h0020179aa7aa0aaa);
      `checkh(par11, 'h19);

      `checkh(par12, 1);  // 9
      `checkh(par13, 3);  // 9, 8, 7
      // See https://www.accellera.org/images/eda/sv-bc/10303.html
      `checkh(par14, 1);  // 3,9
      `checkh(par15, 6);
      `checkh(par16, 0);

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
