// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;
   reg [63:0] crc;
   reg [63:0] sum;

   // Take CRC data and apply to testblock inputs
   wire [32:0] in = crc[32:0];

   logic       bank_rd_vec_m3;
   always_ff @(posedge clk) bank_rd_vec_m3 <= crc[33];

   logic [3:0][31:0] data_i;
   wire [3:0]        out;
   for (genvar i = 0; i < 4; ++i) begin
      always_ff @(posedge clk) data_i[i] <= crc[63:32];
      ecc_check_pipe u_bank_data_ecc_check(
                                           .clk          (clk),
                                           .bank_rd_m3  (bank_rd_vec_m3),
                                           .data_i      ({1'b0, data_i[i]}),
                                           .ecc_err_o   (out[i])
                                           );
   end

   // Aggregate outputs into a single result vector
   wire [63:0] result = {60'b0, out};

   // Test loop
   always @ (posedge clk) begin
`ifdef TEST_VERBOSE
      $write("[%0t] cyc==%0d crc=%x result=%x\n", $time, cyc, crc, result);
`endif
      cyc <= cyc + 1;
      crc <= {crc[62:0], crc[63] ^ crc[2] ^ crc[0]};
      sum <= result ^ {sum[62:0], sum[63] ^ sum[2] ^ sum[0]};
      if (cyc == 0) begin
         // Setup
         crc <= 64'h5aef0c8d_d70a4497;
         sum <= '0;
      end
      else if (cyc < 10) begin
         sum <= '0;
      end
      else if (cyc == 99) begin
         $write("[%0t] cyc==%0d crc=%x sum=%x\n", $time, cyc, crc, sum);
         if (crc !== 64'hc77bb9b3784ea091) $stop;
         // What checksum will we end up with (above print should match)
`define EXPECTED_SUM 64'ha2601675a6ae4972
         if (sum !== `EXPECTED_SUM) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module  ecc_check_pipe (
                        input logic        clk,
                        input logic        bank_rd_m3,
                        input logic [32:0] data_i,
                        output logic       ecc_err_o
                        );
   logic [3:0]                             check_group_6_0;
   logic                                   check_group_6_0_q;

   always_comb check_group_6_0 = {data_i[0], data_i[2], data_i[4], data_i[7] };
   always_ff @(posedge clk) if (bank_rd_m3)  check_group_6_0_q <=^check_group_6_0;
   assign ecc_err_o = check_group_6_0_q;
endmodule
