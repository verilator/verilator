////////////////////////////////////////////////////////////////////////////////
//                                                                            //
// This file is placed into the Public Domain, for any use, without warranty. //
// 2012 by Iztok Jeras                                                        //
// SPDX-License-Identifier: CC0-1.0                                         //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

import package_bus::*;
import package_str::*;
import package_uni::*;

module sv_bus_mux_demux_mux (
  // system signals
  input  logic        clk,      // clock
  input  logic        rst,      // reset
  // input bus
  input  logic        bus_vld,  // valid (chip select)
  input  logic [31:0] bus_adr,  // address
  input  logic [31:0] bus_dat,  // data
  output logic        bus_rdy,  // ready (acknowledge)
  // output stream
  output logic        str_vld,  // valid (chip select)
  output logic  [7:0] str_bus,  // byte data bus
  input  logic        str_rdy   // ready (acknowledge)
);

logic       bus_trn;  // bus    data transfer
logic       str_trn;  // stream data transfer

logic [2:0] pkt_cnt;  // packet byte counter
logic       pkt_end;  // packet byte counter end

//t_bus       pkt_bus;  // transfer packet as a structure
//t_str       pkt_str;  // transfer packet as an array
t_uni       pkt_uni;  // transfer packet as an union

// bus data transfer
assign bus_trn = bus_vld & bus_rdy;

// ready if pipe is empty or output is ready
assign bus_rdy = ~str_vld | pkt_end;

// writing input address/data into a structure
always @ (posedge clk)
if (bus_trn) begin
  pkt_uni.bus.adr <= bus_adr;
  pkt_uni.bus.dat <= bus_dat;
end

// output valid is set by an input transfer
// or cleared by the last output transfer
always @ (posedge clk, posedge rst)
if (rst)           str_vld <= 1'b0;
else               str_vld <= bus_trn | (str_vld & ~pkt_end);

// packet byte counter
always @ (posedge clk, posedge rst)
if (rst)           pkt_cnt <= '0;
else if (str_trn)  pkt_cnt <= pkt_cnt + 3'd1;

// packet byte counter end
assign pkt_end = str_rdy & (&pkt_cnt);

// TODO, this should be a registered signal
assign str_bus = pkt_uni.str [pkt_cnt];

// stream data transfer
assign str_trn = str_vld & str_rdy;

endmodule : sv_bus_mux_demux_mux
