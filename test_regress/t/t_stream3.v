// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2014 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;
   /*AUTOWIRE*/

   generate
      for (genvar width=1; width<=16; width++) begin
         for (genvar amt=1; amt<=width; amt++) begin
            Test #(.WIDTH(width),
                   .AMT(amt))
            test (.ins(crc[width-1:0]));
         end
      end
   endgenerate

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x\n",
             $time, cyc, crc);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= 64'h0;
      end
      else if (cyc<10) begin
         sum <= 64'h0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h0
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Inputs
   ins
   );

   parameter WIDTH = 1;
   parameter AMT = 1;

   input [WIDTH-1:0] ins;
   reg [WIDTH-1:0]  got;
   reg [WIDTH-1:0]  expec;
   int              istart;
   int              bitn;
   int              ostart;

   always @* begin
      got = { << AMT {ins}};

      // Note always starts with right-most bit
      expec = 0;
      for (istart=0; istart<WIDTH; istart+=AMT) begin
         ostart = WIDTH - AMT - istart;
         if (ostart<0) ostart = 0;
         for (bitn=0; bitn<AMT; bitn++) begin
            if ((istart+bitn) < WIDTH
                && (istart+bitn) >= 0
                && (ostart+bitn) < WIDTH
                && (ostart+bitn) >= 0) begin
               expec[ostart+bitn] = ins[istart+bitn];
            end
         end
      end

`ifdef TEST_VERBOSE
      $write("[%0t] exp %0d'b%b got %0d'b%b = { << %0d { %0d'b%b }}\n", $time, WIDTH, expec, WIDTH, got, AMT, WIDTH, ins);
`endif
      `checkh(got, expec);
   end

endmodule
