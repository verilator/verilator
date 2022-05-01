// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2005 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // verilator lint_off LITENDIAN
   // verilator lint_off BLKANDNBLK
   //               3    3    4
   reg [71:0] memw [2:0][1:3][5:2];
   reg [7:0]  memn [2:0][1:3][5:2];
   // verilator lint_on  BLKANDNBLK

   integer cyc; initial cyc = 0;
   reg [63:0] crc;
   reg [71:0] wide;
   reg [7:0]  narrow;
   reg [1:0]  index0;
   reg [1:0]  index1;
   reg [2:0]  index2;
   integer    i0,i1,i2;

   integer    imem[2:0][1:3];
   reg [2:0]  cstyle[2];
   // verilator lint_on  LITENDIAN

   initial begin
      for (i0=0; i0<3; i0=i0+1) begin
         for (i1=1; i1<4; i1=i1+1) begin
            imem[i0[1:0]] [i1[1:0]] = i1;
            for (i2=2; i2<6; i2=i2+1) begin
               memw[i0[1:0]] [i1[1:0]] [i2[2:0]] = {56'hfe_fee0_fee0_fee0_,4'b0,i0[3:0],i1[3:0],i2[3:0]};
               memn[i0[1:0]] [i1[1:0]] [i2[2:0]] = 8'b1000_0001;
            end
         end
      end
   end

   reg [71:0] wread;
   reg        wreadb;

   always @ (posedge clk) begin
      //$write("cyc==%0d crc=%x i[%d][%d][%d] nar=%x wide=%x\n",cyc, crc, index0,index1,index2, narrow, wide);
      cyc <= cyc + 1;
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         narrow <= 8'h0;
         wide   <= 72'h0;
         index0 <= 2'b0;
         index1 <= 2'b0;
         index2 <= 3'b0;
      end
      else if (cyc<90) begin
         index0 <= crc[1:0];
         index1 <= crc[3:2];
         index2 <= crc[6:4];
         crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};

         // We never read past bounds, or get unspecific results
         // We also never read lowest indexes, as writing outside of range may corrupt them
         if (index0>=0+1 && index0<=2 && index1>=1+1 /*&& index1<=3 CMPCONST*/ && index2>=2+1 && index2<=5) begin
            narrow <= ({narrow[6:0], narrow[7]^narrow[0]}
                       ^ {memn[index0][index1][index2]});
            wread   = memw[index0][index1][index2];
            wreadb  = memw[index0][index1][index2][2];
            wide   <= ({wide[70:0], wide[71]^wide[2]^wide[0]} ^ wread);
            //$write("Get memw[%d][%d][%d] -> %x\n",index0,index1,index2, wread);
         end
         // We may write past bounds of memory
         memn[index0][index1][index2]   [crc[10:8]+:3] <= crc[2:0];
         memn[index0][index1][index2]   <= {~crc[6:0],crc[7]};
         memw[index0][index1][index2]   <= {~crc[7:0],crc};
         //$write("Set memw[%d][%d][%d] <= %x\n",index0,index1,index2, {~crc[7:0],crc});
         cstyle[cyc[0]] <= cyc[2:0];
         if (cyc>20) if (cstyle[~cyc[0]] != (cyc[2:0]-3'b1)) $stop;
      end
      else if (cyc==90) begin
         memn[0][1][3] <= memn[0][1][3] ^ 8'ha8;
      end
      else if (cyc==91) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x nar=%x wide=%x\n", $time, cyc, crc, narrow, wide);
         if (crc != 64'h65e3bddcd9bc2750) $stop;
         if (narrow != 8'hca) $stop;
         if (wide !=  72'h4edafed31ba6873f73) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
