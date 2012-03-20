////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// This file is placed into the Public Domain, for any use, without warranty. //
// 2012 by Iztok Jeras                                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// This wrapper contains a bus multiplexer and a bus demultiplexer. Both      //
// modules have all ports exposed an there are no signals connecting them.    //
//                                                                            //
//                           ---------------------                            //
//                           |        wrap       |                            //
//                           |                   |                            //
//                           |    -----------    |                            //
//                   bsi ->  | -> |   mux   | -> | -> sto                     //
//                           |    -----------    |                            //
//                           |                   |                            //
//                           |    -----------    |                            //
//                   bso <-  | <- |  demux  | <- | <- sto                     //
//                           |    -----------    |                            //
//                           |                   |                            //
//                           ---------------------                            //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module sv_bus_mux_demux_wrap (
  // system signals
  input  logic        clk,
  input  logic        rst,
  // input bus
  input  logic        bsi_vld,  // valid (chip select)
  input  logic [31:0] bsi_adr,  // address
  input  logic [31:0] bsi_dat,  // data
  output logic        bsi_rdy,  // ready (acknowledge)
  // output stream
  output logic        sto_vld,
  output logic  [7:0] sto_bus,
  input  logic        sto_rdy,
  // input stream
  input  logic        sti_vld,
  input  logic  [7:0] sti_bus,
  output logic        sti_rdy,
  // output bus
  output logic        bso_vld,  // valid (chip select)
  output logic [31:0] bso_adr,  // address
  output logic [31:0] bso_dat,  // data
  input  logic        bso_rdy   // ready (acknowledge)
);

sv_bus_mux_demux_mux mux (
  // system signals
  .clk      (clk),
  .rst      (rst),
  // input bus
  .bus_vld  (bsi_vld),
  .bus_adr  (bsi_adr),
  .bus_dat  (bsi_dat),
  .bus_rdy  (bsi_rdy),
  // output stream
  .str_vld  (sto_vld),
  .str_bus  (sto_bus),
  .str_rdy  (sto_rdy)
);

sv_bus_mux_demux_demux demux (
  // system signals
  .clk      (clk),
  .rst      (rst),
  // input stream
  .str_vld  (sti_vld),
  .str_bus  (sti_bus),
  .str_rdy  (sti_rdy),
  // output bus
  .bus_vld  (bso_vld),
  .bus_adr  (bso_adr),
  .bus_dat  (bso_dat),
  .bus_rdy  (bso_rdy)
);

endmodule : sv_bus_mux_demux_wrap
