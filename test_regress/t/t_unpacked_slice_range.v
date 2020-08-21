// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA

module t (
   clk
   );
   input clk;

   int c = 0;

   t2 #(0) i_0(.*);
   t2 #(-1) i_1(.*); // lo is -1, hi is 5
   t2 #(-4) i_2(.*); // lo is -4, hi is 1
   t2 #(-10) i_3(.*); // lo is -10, hi is -4
   t2 #(+1) i_4(.*); // lo is 1, hi is 7
   t2 #(+4) i_5(.*); // lo is 4, hi is 10
   t2 #(+10) i_6(.*); // lo is 10, hi is 16

   always @(posedge clk) begin
      c <= c + 1;
      if (c == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module t2 #(parameter ORIGIN = 0) (input wire clk, input int c);
   localparam WIDTH = 7;
   localparam OFFSET = 3;
   localparam FULL_LO = ORIGIN;
   localparam FULL_HI = ORIGIN + WIDTH - 1;
   localparam PART_LO = FULL_LO + OFFSET;
   localparam PART_HI = FULL_HI;
   logic unpack_sig0 [FULL_LO:FULL_HI];
   logic unpack_sig1 [PART_LO:PART_HI];
   logic unpack_sig2 [FULL_HI:FULL_LO];
   logic unpack_sig3 [PART_HI:PART_LO];
   initial $display("%m ORIGIN:%d [%d:%d] [%d:%d]", ORIGIN, FULL_LO, FULL_HI, PART_LO, PART_HI);

   always @(posedge clk) begin
      unpack_sig0[PART_LO] <= 1'b1;
      unpack_sig1[PART_LO] <= 1'b1;
      unpack_sig0 [PART_LO+1:FULL_HI] <= unpack_sig0[PART_LO:FULL_HI-1];
      unpack_sig1 [PART_LO+1:PART_HI] <= unpack_sig1[PART_LO:PART_HI-1];
      unpack_sig2[PART_LO] <= 1'b1;
      unpack_sig3[PART_LO] <= 1'b1;
      unpack_sig2 [FULL_HI:PART_LO+1] <= unpack_sig2[FULL_HI-1:PART_LO];
      unpack_sig3 [PART_HI:PART_LO+1] <= unpack_sig3[PART_HI-1:PART_LO];
   end

   always @(posedge clk) begin
      if (c >= 4) begin
         if (!unpack_sig0[FULL_HI] || !unpack_sig1[PART_HI]) $stop;
         if (!unpack_sig2[FULL_HI] || !unpack_sig3[PART_HI]) $stop;
      end else begin
         if (unpack_sig0[FULL_HI] || unpack_sig1[PART_HI]) $stop;
         if (unpack_sig2[FULL_HI] || unpack_sig3[PART_HI]) $stop;
      end
   end
endmodule
