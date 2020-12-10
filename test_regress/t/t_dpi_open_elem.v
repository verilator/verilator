// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/);

   bit i_bit_p0_u1 [2:-2];
   bit o_bit_p0_u1 [2:-2];
   bit q_bit_p0_u1 [2:-2];
   bit i_bit_p0_u2 [2:-2] [-3:3];
   bit o_bit_p0_u2 [2:-2] [-3:3];
   bit q_bit_p0_u2 [2:-2] [-3:3];
   bit i_bit_p0_u3 [2:-2] [-3:3] [4:-4];
   bit o_bit_p0_u3 [2:-2] [-3:3] [4:-4];
   bit q_bit_p0_u3 [2:-2] [-3:3] [4:-4];
   import "DPI-C" function void dpii_bit_elem_p0_u1
     (int p, int u, input bit i [], output bit o [], output bit q []);
   import "DPI-C" function void dpii_bit_elem_p0_u2
     (int p, int u, input bit i [] [], output bit o [] [], output bit q [] []);
   import "DPI-C" function void dpii_bit_elem_p0_u3
     (int p, int u, input bit i [] [] [], output bit o [] [] [], output bit q [] [] []);

   logic i_logic_p0_u1 [2:-2];
   logic o_logic_p0_u1 [2:-2];
   logic q_logic_p0_u1 [2:-2];
   logic i_logic_p0_u2 [2:-2] [-3:3];
   logic o_logic_p0_u2 [2:-2] [-3:3];
   logic q_logic_p0_u2 [2:-2] [-3:3];
   logic i_logic_p0_u3 [2:-2] [-3:3] [4:-4];
   logic o_logic_p0_u3 [2:-2] [-3:3] [4:-4];
   logic q_logic_p0_u3 [2:-2] [-3:3] [4:-4];
   import "DPI-C" function void dpii_logic_elem_p0_u1(int p, int u, input logic i [],
                                                         output logic o [], output logic q []);
   import "DPI-C" function void dpii_logic_elem_p0_u2(int p, int u, input logic i [] [],
                                                         output logic o [] [], output logic q [] []);
   import "DPI-C" function void dpii_logic_elem_p0_u3(int p, int u, input logic i [] [] [],
                                                         output logic o [] [] [], output logic q [] [] []);

   import "DPI-C" function int dpii_failure();

   reg [95:0] crc;

   initial begin
      crc = 96'h8a10a572_5aef0c8d_d70a4497;

      begin
         for (int a=-2; a<=2; a=a+1) begin
            i_bit_p0_u1[a] = crc[0];
            for (int b=-3; b<=3; b=b+1) begin
               i_bit_p0_u2[a][b] = crc[0];
               for (int c=-4; c<=4; c=c+1) begin
                  i_bit_p0_u3[a][b][c] = crc[0];
                  crc = {crc[94:0], crc[95]^crc[2]^crc[0]};
               end
            end
         end
         dpii_bit_elem_p0_u1(0, 1, i_bit_p0_u1, o_bit_p0_u1, q_bit_p0_u1);
         dpii_bit_elem_p0_u2(0, 2, i_bit_p0_u2, o_bit_p0_u2, q_bit_p0_u2);
         dpii_bit_elem_p0_u3(0, 3, i_bit_p0_u3, o_bit_p0_u3, q_bit_p0_u3);
         for (int a=-2; a<=2; a=a+1) begin
            `checkh(o_bit_p0_u1[a], ~i_bit_p0_u1[a]);
            `checkh(q_bit_p0_u1[a], ~i_bit_p0_u1[a]);
            for (int b=-3; b<=3; b=b+1) begin
               `checkh(o_bit_p0_u2[a][b], ~i_bit_p0_u2[a][b]);
               `checkh(q_bit_p0_u2[a][b], ~i_bit_p0_u2[a][b]);
               for (int c=-4; c<=4; c=c+1) begin
                  `checkh(o_bit_p0_u3[a][b][c], ~i_bit_p0_u3[a][b][c]);
                  `checkh(q_bit_p0_u3[a][b][c], ~i_bit_p0_u3[a][b][c]);
               end
            end
         end
      end

      begin
         for (int a=-2; a<=2; a=a+1) begin
            i_logic_p0_u1[a] = crc[0];
            for (int b=-3; b<=3; b=b+1) begin
               i_logic_p0_u2[a][b] = crc[0];
               for (int c=-4; c<=4; c=c+1) begin
                  i_logic_p0_u3[a][b][c] = crc[0];
                  crc = {crc[94:0], crc[95]^crc[2]^crc[0]};
               end
            end
         end
         dpii_logic_elem_p0_u1(0, 1, i_logic_p0_u1, o_logic_p0_u1, q_logic_p0_u1);
         dpii_logic_elem_p0_u2(0, 2, i_logic_p0_u2, o_logic_p0_u2, q_logic_p0_u2);
         dpii_logic_elem_p0_u3(0, 3, i_logic_p0_u3, o_logic_p0_u3, q_logic_p0_u3);
         for (int a=-2; a<=2; a=a+1) begin
            `checkh(o_logic_p0_u1[a], ~i_logic_p0_u1[a]);
            `checkh(q_logic_p0_u1[a], ~i_logic_p0_u1[a]);
            for (int b=-3; b<=3; b=b+1) begin
               `checkh(o_logic_p0_u2[a][b], ~i_logic_p0_u2[a][b]);
               `checkh(q_logic_p0_u2[a][b], ~i_logic_p0_u2[a][b]);
               for (int c=-4; c<=4; c=c+1) begin
                  `checkh(o_logic_p0_u3[a][b][c], ~i_logic_p0_u3[a][b][c]);
                  `checkh(q_logic_p0_u3[a][b][c], ~i_logic_p0_u3[a][b][c]);
               end
            end
         end
      end

      if (dpii_failure()!=0) begin
         $write("%%Error: Failure in DPI tests\n");
         $stop;
      end
      else begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
