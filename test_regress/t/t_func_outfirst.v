// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define DDIFF_BITS 9
`define AOA_BITS 8
`define HALF_DDIFF `DDIFF_BITS'd256
`define MAX_AOA `AOA_BITS'd255
`define BURP_DIVIDER 9'd16

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc = 0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [`DDIFF_BITS-1:0] DDIFF_B = crc[`DDIFF_BITS-1:0];
   wire reset = (cyc<7);

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [`AOA_BITS-1:0] AOA_B;                  // From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
              // Outputs
              .AOA_B                    (AOA_B[`AOA_BITS-1:0]),
              // Inputs
              .DDIFF_B                  (DDIFF_B[`DDIFF_BITS-1:0]),
              .reset                    (reset),
              .clk                      (clk));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {56'h0, AOA_B};

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
`define EXPECTED_SUM 64'h3a74e9d34771ad93
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module Test (/*AUTOARG*/
   // Outputs
   AOA_B,
   // Inputs
   DDIFF_B, reset, clk
   );

   input [`DDIFF_BITS-1:0] DDIFF_B;
   input reset;
   input clk;
   output reg [`AOA_BITS-1:0] AOA_B;

   reg [`AOA_BITS-1:0] AOA_NEXT_B;
   reg [`AOA_BITS-1:0] tmp;

   always @(posedge clk) begin
      if (reset) begin
         AOA_B <= 8'h80;
      end
      else begin
         AOA_B <= AOA_NEXT_B;
      end
   end

   always @* begin
      // verilator lint_off WIDTH
      tmp = ((`HALF_DDIFF-DDIFF_B)/`BURP_DIVIDER);
      t_aoa_update(AOA_NEXT_B, AOA_B, ((`HALF_DDIFF-DDIFF_B)/`BURP_DIVIDER));
      // verilator lint_on WIDTH
   end

   task t_aoa_update;
      output [`AOA_BITS-1:0] aoa_reg_next;
      input [`AOA_BITS-1:0] aoa_reg;
      input [`AOA_BITS-1:0] aoa_delta_update;
      begin
         if ((`MAX_AOA-aoa_reg)<aoa_delta_update) //Overflow protection
           aoa_reg_next=`MAX_AOA;
         else
           aoa_reg_next=aoa_reg+aoa_delta_update;
      end
   endtask
endmodule
