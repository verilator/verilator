// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2017 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

//`ifdef VERILATOR
 `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)
//`else
// `define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); end while(0)
//`endif

module t (/*AUTOARG*/);

   // verilator lint_off UNUSED
   reg        i_rl_p0_u1 [-2:2];
   reg        o_rl_p0_u1 [-2:2];
   reg [1:-1] i_rl_p1_u1 [-2:2];
   reg [1:-1] o_rl_p1_u1 [-2:2];
   reg [1:-1] i_rl_p1_u2 [-2:2] [-3:3];
   reg [1:-1] o_rl_p1_u2 [-2:2] [-3:3];
   reg [1:-1] i_rl_p1_u3 [-2:2] [-3:3] [-4:4];
   reg [1:-1] o_rl_p1_u3 [-2:2] [-3:3] [-4:4];

   reg        i_rb_p0_u1 [2:-2];
   reg        o_rb_p0_u1 [2:-2];
   reg [1:-1] i_rb_p1_u1 [2:-2];
   reg [1:-1] o_rb_p1_u1 [2:-2];
   reg [1:-1] i_rb_p1_u2 [2:-2] [3:-3];
   reg [1:-1] o_rb_p1_u2 [2:-2] [3:-3];
   reg [1:-1] i_rb_p1_u3 [2:-2] [3:-3] [4:-4];
   reg [1:-1] o_rb_p1_u3 [2:-2] [3:-3] [4:-4];

   reg        i_rw_p0_u1 [2:-2];
   reg        o_rw_p0_u1 [2:-2];
   reg [95:1] i_rw_p1_u1 [2:-2];
   reg [95:1] o_rw_p1_u1 [2:-2];
   reg [95:1] i_rw_p1_u2 [2:-2] [3:-3];
   reg [95:1] o_rw_p1_u2 [2:-2] [3:-3];
   reg [95:1] i_rw_p1_u3 [2:-2] [3:-3] [4:-4];
   reg [95:1] o_rw_p1_u3 [2:-2] [3:-3] [4:-4];

   bit        i_bit [1:0];
   bit        o_bit [1:0];
   logic      i_logic [1:0];
   logic      o_logic [1:0];
   byte       i_byte [1:0];
   byte       o_byte [1:0];
   integer    i_integer [1:0];
   integer    o_integer [1:0];

   import "DPI-C" function int dpii_failure();

   import "DPI-C" function void dpii_unused(input reg u []);

   // [] on packed arrays is unsupported in VCS & NC, so not supporting this

   // p is number of packed dimensions, u is number of unpacked dimensions
   import "DPI-C" function void dpii_open_p0_u1(input int c,p,u, input reg i [], output reg o []);
   import "DPI-C" function void dpii_open_p1_u1(input int c,p,u, input reg [1:-1] i [], output reg [1:-1] o []);
   import "DPI-C" function void dpii_open_p1_u2(input int c,p,u, input reg [1:-1] i [] [], output reg [1:-1] o [] []);
   import "DPI-C" function void dpii_open_p1_u3(input int c,p,u, input reg [1:-1] i [] [] [], output reg [1:-1] o [] [] []);

   import "DPI-C" function void dpii_open_pw_u1(input int c,p,u, input reg [95:1] i [], output reg [95:1] o []);
   import "DPI-C" function void dpii_open_pw_u2(input int c,p,u, input reg [95:1] i [] [], output reg [95:1] o [] []);
   import "DPI-C" function void dpii_open_pw_u3(input int c,p,u, input reg [95:1] i [] [] [], output reg [95:1] o [] [] []);

   import "DPI-C" function void dpii_open_bit(input bit i [], output bit o []);
   import "DPI-C" function void dpii_open_logic(input logic i [], output logic o []);
   import "DPI-C" function void dpii_open_byte(input byte i [], output byte o []);
   import "DPI-C" function void dpii_open_integer(input integer i [], output integer o []);

   int        i_int_u1 [2:-2];
   int        o_int_u1 [2:-2];
   int        i_int_u2 [2:-2] [-3:3];
   int        o_int_u2 [2:-2] [-3:3];
   int        i_int_u3 [2:-2] [-3:3] [4:-4];
   int        o_int_u3 [2:-2] [-3:3] [4:-4];
   import "DPI-C" function void dpii_open_int_u1(int u, input int i [], output int o []);
   import "DPI-C" function void dpii_open_int_u2(int u, input int i [] [], output int o [] []);
   import "DPI-C" function void dpii_open_int_u3(int u, input int i [] [] [], output int o [] [] []);

   // verilator lint_on UNUSED

   reg [95:0] crc;

   initial begin
      crc = 96'h8a10a572_5aef0c8d_d70a4497;

      for (int a=0; a<2; a=a+1) begin
         i_bit[a] = crc[0];
         i_logic[a] = crc[0];
         i_byte[a] = crc[7:0];
         i_integer[a] = crc[31:0];
         crc = {crc[94:0], crc[95]^crc[2]^crc[0]};
      end

      dpii_open_bit(i_bit, o_bit);
      dpii_open_logic(i_logic, o_logic);
      dpii_open_byte(i_byte, o_byte);
      dpii_open_integer(i_integer, o_integer);

      for (int a=-2; a<=2; a=a+1) begin
         i_rl_p0_u1[a] = crc[0];
         i_rb_p0_u1[a] = crc[0];
         i_rw_p0_u1[a] = crc[0];
         i_rl_p1_u1[a] = crc[2:0];
         i_rb_p1_u1[a] = crc[2:0];
         i_rw_p1_u1[a] = crc[94:0];
         i_int_u1[a] = crc[31:0];
         for (int b=-3; b<=3; b=b+1) begin
            i_rl_p1_u2[a][b] = crc[2:0];
            i_rb_p1_u2[a][b] = crc[2:0];
            i_rw_p1_u2[a][b] = crc[94:0];
            i_int_u2[a][b] = crc[31:0];
            for (int c=-4; c<=4; c=c+1) begin
               i_rl_p1_u3[a][b][c] = crc[2:0];
               i_rb_p1_u3[a][b][c] = crc[2:0];
               i_rw_p1_u3[a][b][c] = crc[94:0];
               i_int_u3[a][b][c] = crc[31:0];
               crc = {crc[94:0], crc[95]^crc[2]^crc[0]};
            end
         end
      end

      dpii_open_p0_u1(0,0,1, i_rl_p0_u1, o_rl_p0_u1);
      dpii_open_p0_u1(1,0,1, i_rb_p0_u1, o_rb_p0_u1);
      dpii_open_p0_u1(2,0,1, i_rw_p0_u1, o_rw_p0_u1);
      dpii_open_p1_u1(0,1,1, i_rl_p1_u1, o_rl_p1_u1);
      dpii_open_p1_u2(0,1,2, i_rl_p1_u2, o_rl_p1_u2);
      dpii_open_p1_u3(0,1,3, i_rl_p1_u3, o_rl_p1_u3);
      dpii_open_p1_u1(1,1,1, i_rb_p1_u1, o_rb_p1_u1);
      dpii_open_p1_u2(1,1,2, i_rb_p1_u2, o_rb_p1_u2);
      dpii_open_p1_u3(1,1,3, i_rb_p1_u3, o_rb_p1_u3);
      dpii_open_pw_u1(2,1,1, i_rw_p1_u1, o_rw_p1_u1);
      dpii_open_pw_u2(2,1,2, i_rw_p1_u2, o_rw_p1_u2);
      dpii_open_pw_u3(2,1,3, i_rw_p1_u3, o_rw_p1_u3);

      for (int a=-2; a<=2; a=a+1) begin
         for (int b=-3; b<=3; b=b+1) begin
            for (int c=-4; c<=4; c=c+1) begin
               `checkh(o_rw_p1_u3[a][b][c], ~i_rw_p1_u3[a][b][c]);
            end
         end
      end

      dpii_open_int_u1(1, i_int_u1, o_int_u1);
      dpii_open_int_u2(2, i_int_u2, o_int_u2);
      dpii_open_int_u3(3, i_int_u3, o_int_u3);
      for (int a=-2; a<=2; a=a+1) begin
         `checkh(o_int_u1[a], ~i_int_u1[a]);
         for (int b=-3; b<=3; b=b+1) begin
            `checkh(o_int_u2[a][b], ~i_int_u2[a][b]);
            for (int c=-4; c<=4; c=c+1) begin
               `checkh(o_int_u3[a][b][c], ~i_int_u3[a][b][c]);
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
