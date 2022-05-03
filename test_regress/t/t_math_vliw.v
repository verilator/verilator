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
   integer cyc; initial cyc = 0;
   reg [7:0] crc;
   reg [223:0] sum;

   wire [255:0] mglehy = {32{~crc}};
   wire [215:0] drricx = {27{crc}};
   wire [15:0]  apqrli = {2{~crc}};
   wire [2:0]   szlfpf = crc[2:0];
   wire [15:0]  dzosui = {2{crc}};
   wire [31:0]  zndrba = {16{crc[1:0]}};
   wire [223:0] bxiouf;

   vliw vliw (
              // Outputs
              .bxiouf (bxiouf),
              // Inputs
              .mglehy   (mglehy[255:0]),
              .drricx   (drricx[215:0]),
              .apqrli   (apqrli[15:0]),
              .szlfpf   (szlfpf[2:0]),
              .dzosui   (dzosui[15:0]),
              .zndrba   (zndrba[31:0]));

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      crc <= {crc[6:0], ~^ {crc[7],crc[5],crc[4],crc[3]}};
      if (cyc==0) begin
         // Setup
         crc <= 8'hed;
         sum <= 224'h0;
      end
      else if (cyc<90) begin
         //$write("[%0t] cyc==%0d BXI=%x\n", $time, cyc, bxiouf);
         sum <= {sum[222:0],sum[223]} ^ bxiouf;
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%b %x\n", $time, cyc, crc, sum);
         if (crc !== 8'b01110000) $stop;
         if (sum !== 224'h1fdff998855c3c38d467e28124847831f9ad6d4a09f2801098f032a8) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module vliw (
             input[255:0]  mglehy,
             input[215:0]  drricx,
             input[15:0]   apqrli,
             input[2:0]    szlfpf,
             input[15:0]   dzosui,
             input[31:0]   zndrba,
             output wire [223:0] bxiouf
             );

   wire [463:0] zhknfc  =   ({29{~apqrli}} & {mglehy, drricx[215:8]})
                | ({29{apqrli}}  & {mglehy[247:0], drricx});
   wire [335:0] umntwz =   ({21{~dzosui}} & zhknfc[463:128])
                | ({21{dzosui}}  & zhknfc[335:0]);
   wire [335:0] viuvoc = umntwz << {szlfpf, 4'b0000};
   wire [223:0] rzyeut = viuvoc[335:112];
   assign bxiouf       = {rzyeut[7:0],
                          rzyeut[15:8],
                          rzyeut[23:16],
                          rzyeut[31:24],
                          rzyeut[39:32],
                          rzyeut[47:40],
                          rzyeut[55:48],
                          rzyeut[63:56],
                          rzyeut[71:64],
                          rzyeut[79:72],
                          rzyeut[87:80],
                          rzyeut[95:88],
                          rzyeut[103:96],
                          rzyeut[111:104],
                          rzyeut[119:112],
                          rzyeut[127:120],
                          rzyeut[135:128],
                          rzyeut[143:136],
                          rzyeut[151:144],
                          rzyeut[159:152],
                          rzyeut[167:160],
                          rzyeut[175:168],
                          rzyeut[183:176],
                          rzyeut[191:184],
                          rzyeut[199:192],
                          rzyeut[207:200],
                          rzyeut[215:208],
                          rzyeut[223:216]};

endmodule
