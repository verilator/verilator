////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// This file is placed into the Public Domain, for any use, without warranty. //
// 2012 by Iztok Jeras                                                        //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import package_bus::*;
import package_str::*;

module sv_bus_mux_demux_demux (
  // system signals
  input  logic        clk,      // clock
  input  logic        rst,      // reset
  // output stream
  input  logic        str_vld,  // valid (chip select)
  input  logic  [7:0] str_bus,  // byte data bus
  output logic        str_rdy,  // ready (acknowledge)
  // input bus
  output logic        bus_vld,  // valid (chip select)
  output logic [31:0] bus_adr,  // address
  output logic [31:0] bus_dat,  // data
  input  logic        bus_rdy   // ready (acknowledge)
);

logic       bus_trn;  // bus    data transfer
logic       str_trn;  // stream data transfer

logic [2:0] pkt_cnt;  // packet byte counter
logic       pkt_end;  // packet byte counter end

t_str       pkt_str;  // transfer packet as a structure
t_bus       pkt_bus;  // transfer packet as an array

// stream data transfer
assign str_trn = str_vld & str_rdy;

// ready if pipe is empty or output is ready
assign str_rdy = ~bus_vld | bus_rdy;

// packet byte counter
always @ (posedge clk, posedge rst)
if (rst)           pkt_cnt <= 3'd0;
else if (str_trn)  pkt_cnt <= pkt_cnt + 3'd1;

// packet byte counter end
assign pkt_end = (&pkt_cnt);

always @ (posedge clk)
if (str_trn)  pkt_str [pkt_cnt] <= str_bus;

// the input packed array is mapped onto the output structure
assign pkt_bus = pkt_str;

// the output structure is mapped onto address/data outputs
assign bus_adr = pkt_bus.adr;
assign bus_dat = pkt_bus.dat;

// output valid is set on the last input packed byte
// or cleared by each output transfer
always @ (posedge clk, posedge rst)
if (rst)  bus_vld <= 1'b0;
else      bus_vld <= str_trn & pkt_end | bus_vld & ~bus_rdy;

// bus data transfer
assign bus_trn = bus_vld & bus_rdy;

endmodule : sv_bus_mux_demux_demux
