// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2008 by Lane Brooks.
// SPDX-License-Identifier: CC0-1.0
//
// This implements a 4096:1 mux via two stages of 64:1 muxing.

// change these two parameters to see the speed differences
//`define DATA_WIDTH 12
//`define MUX2_SIZE 32
`define DATA_WIDTH 2
`define MUX2_SIZE 8

// if you change these, then the testbench will break
`define ADDR_WIDTH 12
`define MUX1_SIZE 64

// Total of DATA_WIDTH*MUX2_SIZE*(MUX1_SIZE+1) instantiations of mux64

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   /*AUTOWIRE*/
   // Beginning of automatic wires (for undeclared instantiated-module outputs)
   wire [`DATA_WIDTH-1:0] datao;                // From mux4096 of mux4096.v
   // End of automatics

   reg [`DATA_WIDTH*`MUX1_SIZE*`MUX2_SIZE-1:0] datai;
   reg [`ADDR_WIDTH-1:0]                       addr;

   // Mux: takes in addr and datai and outputs datao
   mux4096 mux4096 (/*AUTOINST*/
                    // Outputs
                    .datao              (datao[`DATA_WIDTH-1:0]),
                    // Inputs
                    .datai              (datai[`DATA_WIDTH*`MUX1_SIZE*`MUX2_SIZE-1:0]),
                    .addr               (addr[`ADDR_WIDTH-1:0]));


   // calculate what the answer should be from datai.  This is bit
   // tricky given the way datai gets sliced.  datai is in bit
   // planes where all the LSBs are contiguous and then the next bit.
   reg [`DATA_WIDTH-1:0] datao_check;
   integer j;
   always @(datai or addr) begin
      for(j=0;j<`DATA_WIDTH;j=j+1) begin
         /* verilator lint_off WIDTH */
         datao_check[j] = datai >> ((`MUX1_SIZE*`MUX2_SIZE*j)+addr);
         /* verilator lint_on WIDTH */
      end
   end

   // Run the test loop.  This just increments the address
   integer i, result;
   always @ (posedge clk) begin
      // initial the input data with random values
      if (addr == 0) begin
         result = 1;
         datai = 0;
         for(i=0; i<`MUX1_SIZE*`MUX2_SIZE; i=i+1) begin
            /* verilator lint_off WIDTH */
            datai = (datai << `DATA_WIDTH) | ($random & {`DATA_WIDTH{1'b1}});
            /* verilator lint_on WIDTH */
         end
      end

      addr <= addr + 1;
      if (datao_check != datao) begin
         result = 0;
         $stop;
      end

`ifdef TEST_VERBOSE
      $write("Addr=%d datao_check=%d datao=%d\n", addr, datao_check, datao);
`endif
      // only run the first 10 addresses for now
      if (addr > 10) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module mux4096
  (input [`DATA_WIDTH*`MUX1_SIZE*`MUX2_SIZE-1:0] datai,
   input [`ADDR_WIDTH-1:0] addr,
   output [`DATA_WIDTH-1:0] datao
   );

   // DATA_WIDTH instantiations of mux4096_1bit
   mux4096_1bit mux4096_1bit[`DATA_WIDTH-1:0]
     (.addr(addr),
      .datai(datai),
      .datao(datao)
      );
endmodule

module mux4096_1bit
  (input [`MUX1_SIZE*`MUX2_SIZE-1:0] datai,
   input [`ADDR_WIDTH-1:0] addr,
   output datao
   );

   // address decoding
   wire [3:0]  A = (4'b1) << addr[1:0];
   wire [3:0]  B = (4'b1) << addr[3:2];
   wire [3:0]  C = (4'b1) << addr[5:4];
   wire [3:0]  D = (4'b1) << addr[7:6];
   wire [3:0]  E = (4'b1) << addr[9:8];
   wire [3:0]  F = (4'b1) << addr[11:10];

   wire [`MUX2_SIZE-1:0] data0;

   // DATA_WIDTH*(MUX2_SIZE)*MUX1_SIZE instantiations of mux64
   // first stage of 64:1 muxing
   mux64 #(.MUX_SIZE(`MUX1_SIZE)) mux1[`MUX2_SIZE-1:0]
     (.A(A),
      .B(B),
      .C(C),
      .datai(datai),
      .datao(data0));

   // DATA_WIDTH*MUX2_SIZE instantiations of mux64
   // second stage of 64:1 muxing
   mux64 #(.MUX_SIZE(`MUX2_SIZE)) mux2
     (.A(D),
      .B(E),
      .C(F),
      .datai(data0),
      .datao(datao));

endmodule

module mux64
  #(parameter MUX_SIZE=64)
  (input [3:0] A,
   input [3:0] B,
   input [3:0] C,
   input [MUX_SIZE-1:0] datai,
   output datao
   );

   wire [63:0] colSelA = { 16{ A[3:0] }};
   wire [63:0] colSelB = {  4{ {4{B[3]}}, {4{B[2]}}, {4{B[1]}}, {4{B[0]}}}};
   wire [63:0] colSelC = { {16{C[3]}}, {16{C[2]}}, {16{C[1]}}, {16{C[0]}}};

   wire [MUX_SIZE-1:0] data_bus;

   // Note each of these becomes a separate wire.
   //.colSelA(colSelA[MUX_SIZE-1:0]),
   //.colSelB(colSelB[MUX_SIZE-1:0]),
   //.colSelC(colSelC[MUX_SIZE-1:0]),

   drv drv[MUX_SIZE-1:0]
     (.colSelA(colSelA[MUX_SIZE-1:0]),
      .colSelB(colSelB[MUX_SIZE-1:0]),
      .colSelC(colSelC[MUX_SIZE-1:0]),
      .datai(datai),
      .datao(data_bus)
      );

   assign datao = |data_bus;

endmodule

module drv
  (input colSelA,
   input colSelB,
   input colSelC,
   input datai,
   output datao
   );
   assign datao = colSelC & colSelB & colSelA & datai;

endmodule
