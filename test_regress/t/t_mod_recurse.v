// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Sean Moore.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [7:0]  tripline = crc[7:0];

   /*AUTOWIRE*/

   wire         valid;
   wire [3-1:0] value;

   PriorityChoice #(.OCODEWIDTH(3))
   pe (.out(valid), .outN(value[2:0]), .tripline(tripline));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'h0, valid, value};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
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
`define EXPECTED_SUM 64'hc5fc632f816568fb
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module PriorityChoice (out, outN, tripline);
   parameter OCODEWIDTH = 1;
   localparam CODEWIDTH=OCODEWIDTH-1;
   localparam SCODEWIDTH= (CODEWIDTH<1) ? 1 : CODEWIDTH;

   output reg             out;
   output reg [OCODEWIDTH-1:0] outN;
   input wire [(1<<OCODEWIDTH)-1:0] tripline;
   wire                             left;
   wire [SCODEWIDTH-1:0]            leftN;
   wire                             right;
   wire [SCODEWIDTH-1:0]            rightN;

   generate
      if(OCODEWIDTH==1) begin
         assign left = tripline[1];
         assign right = tripline[0];

         always @(*) begin
            out = left || right ;
            if(right) begin outN = {1'b0}; end
            else  begin outN = {1'b1}; end
         end
      end else begin
         PriorityChoice #(.OCODEWIDTH(OCODEWIDTH-1))
         leftMap
           (
            .out(left),
            .outN(leftN),
            .tripline(tripline[(2<<CODEWIDTH)-1:(1<<CODEWIDTH)])
            );
         PriorityChoice #(.OCODEWIDTH(OCODEWIDTH-1))
         rightMap
           (
            .out(right),
            .outN(rightN),
            .tripline(tripline[(1<<CODEWIDTH)-1:0])
            );
         always @(*) begin
            if(right) begin
               out  = right;
               outN = {1'b0, rightN[OCODEWIDTH-2:0]};
            end else begin
               out  = left;
               outN = {1'b1, leftN[OCODEWIDTH-2:0]};
            end
         end
      end
   endgenerate
endmodule
