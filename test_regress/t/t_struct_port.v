// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   bit         b9;
   byte        b1;
   bit         b0;
} pack_t;

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   pack_t in;
   always @* in = crc[9:0];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   pack_t               out;                    // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .out                      (out),
              // Inputs
              .in                       (in));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {54'h0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x in=%x result=%x\n", $time, cyc, crc, in, result);
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
`define EXPECTED_SUM 64'h99c434d9b08c2a8a
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (
             input  pack_t in,
             output pack_t out);

   always @* begin
      out = in;
      out.b1 = in.b1 + 1;
      out.b0 = 1'b1;
   end
endmodule

// Local Variables:
// verilog-typedef-regexp: "_t$"
// End:
