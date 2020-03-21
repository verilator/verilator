////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// This file is placed into the Public Domain, for any use, without warranty. //
// 2012 by Iztok Jeras                                                        //
// SPDX-License-Identifier: CC0-1.0                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// This testbench contains a bus source and a bus drain. The source creates   //
// address and data bus values, while the drain is the final destination of   //
// such pairs. All source and drain transfers are logged into memories, which //
// are used at the end of simulation to check for data transfer correctness.  //
// Inside the RLT wrapper there is a multiplexer and a demultiplexer, they    //
// bus transfers into a 8bit data stream and back. Both stream input and      //
// output are exposed, they are connected together into a loopback.           //
//                                                                            //
//                    -----------  ---------------------                      //
//                    | bso_mem |  |        wrap       |                      //
//                    -----------  |                   |                      //
//       -----------       |       |    -----------    |                      //
//       | bsi src | ------------> | -> |   mux   | -> | -> -   sto           //
//       -----------               |    -----------    |     \                //
//                                 |                   |      | loopback      //
//       -----------               |    -----------    |     /                //
//       | bso drn | <------------ | <- |  demux  | <- | <- -   sti           //
//       -----------       |       |    -----------    |                      //
//                    -----------  |                   |                      //
//                    | bso_mem |  |                   |                      //
//                    -----------  ---------------------                      //
//                                                                            //
// PROTOCOL:                                                                  //
//                                                                            //
// The 'vld' signal is driven by the source to indicate valid data is         //
// available, 'rdy' is used by the drain to indicate is is ready to accept    //
// valid data. A data transfer only happens if both 'vld' & 'rdy' are active. //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

`timescale 1ns/1ps

// include RTL files
`include "t_sv_bus_mux_demux/sv_bus_mux_demux_def.sv"
`include "t_sv_bus_mux_demux/sv_bus_mux_demux_demux.sv"
`include "t_sv_bus_mux_demux/sv_bus_mux_demux_mux.sv"
`include "t_sv_bus_mux_demux/sv_bus_mux_demux_wrap.sv"

module t (/*AUTOARG*/
   // Inputs
   clk
   );

input clk;

parameter SIZ = 10;

// system signals
//logic        clk = 1'b1;  // clock
logic        rst = 1'b1;  // reset
integer      rst_cnt = 0;

// input bus
logic        bsi_vld;  // valid (chip select)
logic [31:0] bsi_adr;  // address
logic [31:0] bsi_dat;  // data
logic        bsi_rdy;  // ready (acknowledge)
logic        bsi_trn;  // data transfer
logic [31:0] bsi_mem [SIZ];
// output stream
logic        sto_vld;  // valid (chip select)
logic  [7:0] sto_bus;  // data bus
logic        sto_rdy;  // ready (acknowledge)

// input stream
logic        sti_vld;  // valid (chip select)
logic  [7:0] sti_bus;  // data bus
logic        sti_rdy;  // ready (acknowledge)
// output bus
logic        bso_vld;  // valid (chip select)
logic [31:0] bso_adr;  // address
logic [31:0] bso_dat;  // data
logic        bso_rdy;  // ready (acknowledge)
logic        bso_trn;  // data transfer
logic [31:0] bso_mem [SIZ];
integer      bso_cnt = 0;

////////////////////////////////////////////////////////////////////////////////
// clock and reset
////////////////////////////////////////////////////////////////////////////////

// clock toggling
//always #5  clk = ~clk;

// reset is removed after a delay
always @ (posedge clk)
begin
  rst_cnt <= rst_cnt + 1;
  rst     <= rst_cnt <= 3;
end

// reset is removed after a delay
always @ (posedge clk)
if (bso_cnt == SIZ) begin
  if (bsi_mem === bso_mem)  begin  $write("*-* All Finished *-*\n"); $finish();  end
  else                      begin  $display ("FAILED"); $stop();  end
end

////////////////////////////////////////////////////////////////////////////////
// input data generator
////////////////////////////////////////////////////////////////////////////////

// input data transfer
assign bsi_trn = bsi_vld & bsi_rdy;

// valid (for SIZ transfers)
always @ (posedge clk, posedge rst)
if (rst)          bsi_vld = 1'b0;
else              bsi_vld = (bsi_adr < SIZ);

// address (increments every transfer)
always @ (posedge clk, posedge rst)
if (rst)          bsi_adr <= 32'h00000000;
else if (bsi_trn) bsi_adr <= bsi_adr + 'd1;

// data (new random value generated after every transfer)
always @ (posedge clk, posedge rst)
if (rst)          bsi_dat <= 32'h00000000;
else if (bsi_trn) bsi_dat <= $random();

// storing transferred data into memory for final check
always @ (posedge clk)
if (bsi_trn) bsi_mem [bsi_adr] <= bsi_dat;

////////////////////////////////////////////////////////////////////////////////
// RTL instance
////////////////////////////////////////////////////////////////////////////////

sv_bus_mux_demux_wrap wrap (
  // system signals
  .clk      (clk),
  .rst      (rst),
  // input bus
  .bsi_vld  (bsi_vld),
  .bsi_adr  (bsi_adr),
  .bsi_dat  (bsi_dat),
  .bsi_rdy  (bsi_rdy),
  // output stream
  .sto_vld  (sto_vld),
  .sto_bus  (sto_bus),
  .sto_rdy  (sto_rdy),
  // input stream
  .sti_vld  (sti_vld),
  .sti_bus  (sti_bus),
  .sti_rdy  (sti_rdy),
  // output bus
  .bso_vld  (bso_vld),
  .bso_adr  (bso_adr),
  .bso_dat  (bso_dat),
  .bso_rdy  (bso_rdy)
);

// stream output from mux is looped back into stream input for demux
assign sti_vld = sto_vld;
assign sti_bus = sto_bus;
assign sto_rdy = sti_rdy;

////////////////////////////////////////////////////////////////////////////////
// output data monitor
////////////////////////////////////////////////////////////////////////////////

// input data transfer
assign bso_trn = bso_vld & bso_rdy;

// output transfer counter used to end the test
always @ (posedge clk, posedge rst)
if (rst)           bso_cnt <= 0;
else if (bso_trn)  bso_cnt <= bso_cnt + 1;

// storing transferred data into memory for final check
always @ (posedge clk)
if (bso_trn)  bso_mem [bso_adr] <= bso_dat;

// every output transfer against expected value stored in memory
always @ (posedge clk)
if (bso_trn && (bsi_mem [bso_adr] !== bso_dat))
$display ("@%08h i:%08h o:%08h", bso_adr, bsi_mem [bso_adr], bso_dat);

// ready is active for SIZ transfers
always @ (posedge clk, posedge rst)
if (rst)  bso_rdy = 1'b0;
else      bso_rdy = 1'b1;

endmodule : sv_bus_mux_demux_tb
