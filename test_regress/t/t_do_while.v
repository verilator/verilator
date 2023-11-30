// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

function automatic int get_1;
   int a = 0;
   do begin
      int x = 1;
      a += x;
   end while (a < 0);
   return a;
endfunction

module t (/*AUTOARG*/);
   int a;
   initial begin
      if (get_1() != 1) $stop;

      a = 0;
      do begin
         int x = 1;
         a += x;
         if (a == 1) begin
            a = 2;
         end
      end while (a < 0);
      if (a != 2) $stop;

      a = 1;
      do begin
         if (a == 1) begin
            a = 2;
         end
         if (a == 2) begin
            a = 3;
         end
      end while (a < 0);
      if (a != 3) $stop;

      a = 1;
      do begin
         if (a == 1) begin
            do begin
               a++;
            end while (a < 5);
         end
         if (a == 2) begin
            a = 3;
         end
      end while (a < 0);
      if (a != 5) $stop;

      a = 1;
      do begin
         do begin
            int x = 1;
            a += x;
         end while (a < 3);
      end while (a < 5);
      if (a != 5) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
