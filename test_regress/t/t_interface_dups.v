// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer      cyc=0;
   reg [63:0]   crc;
   reg [63:0]   sum;

   // Take CRC data and apply to testblock inputs
   wire [4:0]  din_data = crc[4:0];
   wire [0:0]  din_valid = crc[6];
   wire [0:0]  dout0_ready = crc[16];
   wire [0:0]  dout1_ready = crc[17];
   wire [0:0]  dout2_ready = crc[18];

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   logic		din_ready;		// From test of Test.v
   logic [0:0]		dout0_data;		// From test of Test.v
   logic		dout0_valid;		// From test of Test.v
   logic [1:0]		dout1_data;		// From test of Test.v
   logic		dout1_valid;		// From test of Test.v
   logic [2:0]		dout2_data;		// From test of Test.v
   logic		dout2_valid;		// From test of Test.v
   // End of automatics

   Test test (/*AUTOINST*/
	      // Outputs
	      .din_ready		(din_ready),
	      .dout0_valid		(dout0_valid),
	      .dout0_data		(dout0_data[0:0]),
	      .dout1_valid		(dout1_valid),
	      .dout1_data		(dout1_data[1:0]),
	      .dout2_valid		(dout2_valid),
	      .dout2_data		(dout2_data[2:0]),
	      // Inputs
	      .din_valid		(din_valid),
	      .din_data			(din_data[4:0]),
	      .dout0_ready		(dout0_ready),
	      .dout1_ready		(dout1_ready),
	      .dout2_ready		(dout2_ready));

   // Aggregate outputs into a single result vector
   wire [63:0] result = {48'h0, din_ready,
                         2'd0, dout2_valid, dout2_data,
                         2'd0, dout1_valid, dout1_data,
                         2'd0, dout0_valid, dout0_data};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n",$time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63]^crc[2]^crc[0]};
      sum <= result ^ {sum[62:0],sum[63]^sum[2]^sum[0]};
      if (cyc==0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc<10) begin
         sum <= '0;
      end
      else if (cyc<90) begin
      end
      else if (cyc==99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n",$time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'h6fd1bead9df31b07
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

interface dti
  #(W_DATA = 64
    )();

   logic [W_DATA-1:0] data;
   logic              valid;
   logic              ready;

   modport producer (output data,
                     output valid,
                     input  ready);
   modport consumer (input  data,
                     input  valid,
                     output ready);
endinterface : dti

module Test
  (
   output logic       din_ready,
   input logic        din_valid,
   input logic [4:0]  din_data,
   input logic        dout0_ready,
   output logic       dout0_valid,
   output logic [0:0] dout0_data,
   input logic        dout1_ready,
   output logic       dout1_valid,
   output logic [1:0] dout1_data,
   input logic        dout2_ready,
   output logic       dout2_valid,
   output logic [2:0] dout2_data
   );

   // Interface declarations
   dti #(.W_DATA(5)) din();
   dti #(.W_DATA(1)) dout0();
   dti #(.W_DATA(2)) dout1();
   dti #(.W_DATA(3)) dout2();

   // Interface wiring to top level ports
   assign din.valid = din_valid;
   assign din.data = din_data;
   assign din_ready = din.ready;

   assign dout0_valid = dout0.valid;
   assign dout0_data = dout0.data;
   assign dout0.ready = dout0_ready;

   assign dout1_valid = dout1.valid;
   assign dout1_data = dout1.data;
   assign dout1.ready = dout1_ready;

   assign dout2_valid = dout2.valid;
   assign dout2_data = dout2.data;
   assign dout2.ready = dout2_ready;

   assign din.ready = 0;
   assign dout0.data = 0;
   assign dout1.data = 0;
   assign dout2.data = 0;

   typedef struct      packed {
      logic [1:0]      ctrl;
      logic [2:0]      data;
   } din_t;

   din_t din_s;
   assign din_s = din.data;

   always_comb begin
      dout0.valid = 0;
      dout1.valid = 0;
      dout2.valid = 0;

      case (din_s.ctrl)
        0 : dout0.valid = din.valid;
        1 : dout1.valid = din.valid;
        2 : dout2.valid = din.valid;
        default: ;
      endcase
   end
endmodule
