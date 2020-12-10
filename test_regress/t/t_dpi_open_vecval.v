// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/);

   // Note that a packed array is required, otherwise some simulators will return bad
   // results using *ElemVecVal() routines instead of scalar *Elem() routines.
   bit [0:0] i_bit_p1_u1 [2:-2];
   bit [0:0] o_bit_p1_u1 [2:-2];
   bit [0:0] q_bit_p1_u1 [2:-2];
   bit [60:0] i_bit61_p1_u1 [2:-2];
   bit [60:0] o_bit61_p1_u1 [2:-2];
   bit [60:0] q_bit61_p1_u1 [2:-2];
   bit [91:0] i_bit92_p1_u1 [2:-2];
   bit [91:0] o_bit92_p1_u1 [2:-2];
   bit [91:0] q_bit92_p1_u1 [2:-2];
   bit [11:0] i_bit12_p1_u2 [2:-2] [-3:3];
   bit [11:0] o_bit12_p1_u2 [2:-2] [-3:3];
   bit [11:0] q_bit12_p1_u2 [2:-2] [-3:3];
   bit [29:1] i_bit29_p1_u3 [2:-2] [-3:3] [4:-4];
   bit [29:1] o_bit29_p1_u3 [2:-2] [-3:3] [4:-4];
   bit [29:1] q_bit29_p1_u3 [2:-2] [-3:3] [4:-4];
   import "DPI-C" function void dpii_bit_vecval_p1_u1
     (int bits, int p, int u, input bit [0:0] i [], output bit [0:0] o [], output bit [0:0] q []);
   import "DPI-C" function void dpii_bit61_vecval_p1_u1
     (int bits, int p, int u, input bit [60:0] i [], output bit [60:0] o [], output bit [60:0] q []);
   import "DPI-C" function void dpii_bit92_vecval_p1_u1
     (int bits, int p, int u, input bit [91:0] i [], output bit [91:0] o [], output bit [91:0] q []);
   import "DPI-C" function void dpii_bit12_vecval_p1_u2
     (int bits, int p, int u, input bit [11:0] i [] [], output bit [11:0] o [] [], output bit [11:0] q [] []);
   import "DPI-C" function void dpii_bit29_vecval_p1_u3
     (int bits, int p, int u, input bit [29:1] i [] [] [], output bit [29:1] o [] [] [], output bit [29:1] q [] [] []);

   logic [0:0] i_logic_p1_u1 [2:-2];
   logic [0:0] o_logic_p1_u1 [2:-2];
   logic [0:0] q_logic_p1_u1 [2:-2];
   logic [60:0] i_logic61_p1_u1 [2:-2];
   logic [60:0] o_logic61_p1_u1 [2:-2];
   logic [60:0] q_logic61_p1_u1 [2:-2];
   logic [91:0] i_logic92_p1_u1 [2:-2];
   logic [91:0] o_logic92_p1_u1 [2:-2];
   logic [91:0] q_logic92_p1_u1 [2:-2];
   logic [11:0] i_logic12_p1_u2 [2:-2] [-3:3];
   logic [11:0] o_logic12_p1_u2 [2:-2] [-3:3];
   logic [11:0] q_logic12_p1_u2 [2:-2] [-3:3];
   logic [29:1] i_logic29_p1_u3 [2:-2] [-3:3] [4:-4];
   logic [29:1] o_logic29_p1_u3 [2:-2] [-3:3] [4:-4];
   logic [29:1] q_logic29_p1_u3 [2:-2] [-3:3] [4:-4];
   import "DPI-C" function void dpii_logic_vecval_p1_u1
     (int logics, int p, int u, input logic [0:0] i [], output logic [0:0] o [], output logic [0:0] q []);
   import "DPI-C" function void dpii_logic61_vecval_p1_u1
     (int logics, int p, int u, input logic [60:0] i [], output logic [60:0] o [], output logic [60:0] q []);
   import "DPI-C" function void dpii_logic92_vecval_p1_u1
     (int logics, int p, int u, input logic [91:0] i [], output logic [91:0] o [], output logic [91:0] q []);
   import "DPI-C" function void dpii_logic12_vecval_p1_u2
     (int logics, int p, int u, input logic [11:0] i [] [], output logic [11:0] o [] [], output logic [11:0] q [] []);
   import "DPI-C" function void dpii_logic29_vecval_p1_u3
     (int logics, int p, int u, input logic [29:1] i [] [] [], output logic [29:1] o [] [] [], output logic [29:1] q [] [] []);

   import "DPI-C" function int dpii_failure();

   reg [95:0] crc;

   initial begin
      crc = 96'h8a10a572_5aef0c8d_d70a4497;

      begin
         for (int a=-2; a<=2; a=a+1) begin
            i_bit_p1_u1[a] = crc[0];
            i_bit61_p1_u1[a] = crc[60:0];
            i_bit92_p1_u1[a] = crc[91:0];
            for (int b=-3; b<=3; b=b+1) begin
               i_bit12_p1_u2[a][b] = crc[11:0];
               for (int c=-4; c<=4; c=c+1) begin
                  i_bit29_p1_u3[a][b][c] = crc[29:1];
                  crc = {crc[94:0], crc[95]^crc[2]^crc[0]};
               end
            end
         end
         dpii_bit_vecval_p1_u1(1, 1, 1, i_bit_p1_u1, o_bit_p1_u1, q_bit_p1_u1);
         dpii_bit61_vecval_p1_u1(61, 1, 1, i_bit61_p1_u1, o_bit61_p1_u1, q_bit61_p1_u1);
         dpii_bit92_vecval_p1_u1(92, 1, 1, i_bit92_p1_u1, o_bit92_p1_u1, q_bit92_p1_u1);
         dpii_bit12_vecval_p1_u2(12, 1, 2, i_bit12_p1_u2, o_bit12_p1_u2, q_bit12_p1_u2);
         dpii_bit29_vecval_p1_u3(29, 1, 3, i_bit29_p1_u3, o_bit29_p1_u3, q_bit29_p1_u3);
         for (int a=-2; a<=2; a=a+1) begin
            `checkh(o_bit_p1_u1[a], ~i_bit_p1_u1[a]);
            `checkh(q_bit_p1_u1[a], ~i_bit_p1_u1[a]);
            `checkh(o_bit61_p1_u1[a], ~i_bit61_p1_u1[a]);
            `checkh(q_bit61_p1_u1[a], ~i_bit61_p1_u1[a]);
            `checkh(o_bit92_p1_u1[a], ~i_bit92_p1_u1[a]);
            `checkh(q_bit92_p1_u1[a], ~i_bit92_p1_u1[a]);
            for (int b=-3; b<=3; b=b+1) begin
               `checkh(o_bit12_p1_u2[a][b], ~i_bit12_p1_u2[a][b]);
               `checkh(q_bit12_p1_u2[a][b], ~i_bit12_p1_u2[a][b]);
               for (int c=-4; c<=4; c=c+1) begin
                  `checkh(o_bit29_p1_u3[a][b][c], ~i_bit29_p1_u3[a][b][c]);
                  `checkh(q_bit29_p1_u3[a][b][c], ~i_bit29_p1_u3[a][b][c]);
               end
            end
         end
      end

      begin
         for (int a=-2; a<=2; a=a+1) begin
            i_logic_p1_u1[a] = crc[0];
            i_logic61_p1_u1[a] = crc[60:0];
            i_logic92_p1_u1[a] = crc[91:0];
            for (int b=-3; b<=3; b=b+1) begin
               i_logic12_p1_u2[a][b] = crc[11:0];
               for (int c=-4; c<=4; c=c+1) begin
                  i_logic29_p1_u3[a][b][c] = crc[29:1];
                  crc = {crc[94:0], crc[95]^crc[2]^crc[0]};
               end
            end
         end
         dpii_logic_vecval_p1_u1(1, 1, 1, i_logic_p1_u1, o_logic_p1_u1, q_logic_p1_u1);
         dpii_logic61_vecval_p1_u1(61, 1, 1, i_logic61_p1_u1, o_logic61_p1_u1, q_logic61_p1_u1);
         dpii_logic92_vecval_p1_u1(92, 1, 1, i_logic92_p1_u1, o_logic92_p1_u1, q_logic92_p1_u1);
         dpii_logic12_vecval_p1_u2(12, 1, 2, i_logic12_p1_u2, o_logic12_p1_u2, q_logic12_p1_u2);
         dpii_logic29_vecval_p1_u3(29, 1, 3, i_logic29_p1_u3, o_logic29_p1_u3, q_logic29_p1_u3);
         for (int a=-2; a<=2; a=a+1) begin
            `checkh(o_logic_p1_u1[a], ~i_logic_p1_u1[a]);
            `checkh(q_logic_p1_u1[a], ~i_logic_p1_u1[a]);
            `checkh(o_logic61_p1_u1[a], ~i_logic61_p1_u1[a]);
            `checkh(q_logic61_p1_u1[a], ~i_logic61_p1_u1[a]);
            `checkh(o_logic92_p1_u1[a], ~i_logic92_p1_u1[a]);
            `checkh(q_logic92_p1_u1[a], ~i_logic92_p1_u1[a]);
            for (int b=-3; b<=3; b=b+1) begin
               `checkh(o_logic12_p1_u2[a][b], ~i_logic12_p1_u2[a][b]);
               `checkh(q_logic12_p1_u2[a][b], ~i_logic12_p1_u2[a][b]);
               for (int c=-4; c<=4; c=c+1) begin
                  `checkh(o_logic29_p1_u3[a][b][c], ~i_logic29_p1_u3[a][b][c]);
                  `checkh(q_logic29_p1_u3[a][b][c], ~i_logic29_p1_u3[a][b][c]);
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
