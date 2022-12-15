// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;

   function bit test_1;
      int iterations = 0;
      do begin
         iterations++;
         break;
      end
      while (1);
      return iterations == 1;
   endfunction

   function bit test_2;
      int iterations = 0;
      do begin
         break;
         iterations++;
      end
      while (1);
      return iterations == 0;
   endfunction

   function bit test_3;
      do
         break;
      while (1);
      return 1'b1;
   endfunction

   function bit test_4;
      int incr = 0;
      do begin
         incr++;
         break;
         incr++;
      end
      while (1);
      return incr == 1;
   endfunction

   function bit test_5;
      int incr = 0;
      do begin
         do
            incr++;
         while (incr < 9);
         incr++;
         break;
         incr++;
      end
      while (1);
      return incr == 10;
   endfunction

   function bit test_6;
      int incr = 0;
      do begin
         do begin
            incr += 1;
            incr += 2;
         end
         while (incr < 9);
         incr++;
         break;
         incr++;
      end
      while (1);
      return incr == 10;
   endfunction

   function bit test_7;
      int incr = 0;
      do begin
         do begin
            incr += 1;
            break;
            incr += 2;
         end
         while (incr < 9);
         incr++;
         break;
         incr++;
      end
      while (1);
      return incr == 2;
   endfunction

   function bit test_8;
      int incr = 0;
      do begin
         incr++;
         continue;
         incr++;
      end
      while (0);
      return incr == 1;
   endfunction

   function bit test_9;
      int incr = 0;
      do begin
         incr++;
         continue;
         incr++;
      end
      while (incr < 5);
      return incr == 5;
   endfunction

   function bit test_10;
      do begin
         continue;
      end
      while (0);
      return 1'b1;
   endfunction

   function bit test_11;
      int incr = 0;
      do begin
         do
            incr++;
         while (0);
         incr++;
         continue;
         incr++;
      end
      while (incr < 11);
      return incr == 12;
   endfunction

   function bit test_12;
      int incr = 0;
      do begin
         do begin
            incr++;
            continue;
            incr++;
         end
         while (0);
         incr++;
         continue;
         incr++;
      end
      while (incr < 11);
      return incr == 12;
   endfunction

   always @(posedge clk) begin
      bit [11:0] results = {test_1(), test_2(), test_3(), test_4(), test_5(),
                            test_6(), test_7(), test_8(), test_9(), test_10(),
                            test_11(), test_12()};

      if (results == '1) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
      else begin
         $write("Results: %b\n", results);
         $stop;
      end
   end
endmodule
