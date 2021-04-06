// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

interface intf ();
   integer value;
endinterface

module fanout
  #(parameter int N = 1)
   (
    intf upstream,
    intf downstream[N-1:0]
    );

   genvar         i;
   for (i = 0; i < N; i = i + 1)
     assign downstream[i].value = upstream.value;

endmodule

module xbar
  (
   input logic clk,
   input int   cyc,
   intf Masters[1:0]
   );

   localparam NUM_DEMUX_OUT = 2 * 4;
   localparam NUM_MUX_IN = 2 * 4;
   intf demuxOut[NUM_DEMUX_OUT-1:0]();
   intf muxIn[NUM_MUX_IN-1:0]();

   //fan out master connections to the crossbar matrix
   fanout #(.N(4)) fanout_inst0
     (.upstream(Masters[0]),
      .downstream(demuxOut[3:0]));

   fanout #(.N(4)) fanout_inst1
     (.upstream(Masters[1]),
      .downstream(demuxOut[7:4]));

   //the crossbar matrix assignments, done as 1D arrays because verilator doesn't currently support >1D arrays of interfaces
   genvar      slv, mst;
   for (slv = 0; slv < 4; slv = slv + 1) begin
      for (mst = 0; mst < 2; mst = mst + 1) begin
         localparam int muxIdx = (slv*2)+mst;
         localparam int demuxIdx = slv+(mst*4);
         assign muxIn[muxIdx].value = demuxOut[demuxIdx].value;
      end
   end

   always @(posedge clk) begin
      if (cyc == 5) begin
         `checkh(Masters[0].value, 2);
         `checkh(Masters[1].value, 1);
         // The first 4 demuxOut values should have the value of the first Master
         `checkh(demuxOut[0].value, Masters[0].value);
         `checkh(demuxOut[1].value, Masters[0].value);
         `checkh(demuxOut[2].value, Masters[0].value);
         `checkh(demuxOut[3].value, Masters[0].value);
         // The next 4 demuxOut values should have the value of the second Master
         `checkh(demuxOut[4].value, Masters[1].value);
         `checkh(demuxOut[5].value, Masters[1].value);
         `checkh(demuxOut[6].value, Masters[1].value);
         `checkh(demuxOut[7].value, Masters[1].value);
         // Each 2 mux inputs should have one input from each master, in order from low to high
         `checkh(muxIn[0].value, Masters[0].value);
         `checkh(muxIn[1].value, Masters[1].value);
         `checkh(muxIn[2].value, Masters[0].value);
         `checkh(muxIn[3].value, Masters[1].value);
         `checkh(muxIn[4].value, Masters[0].value);
         `checkh(muxIn[5].value, Masters[1].value);
         `checkh(muxIn[6].value, Masters[0].value);
         `checkh(muxIn[7].value, Masters[1].value);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule


module t
  (
   clk
   );
   input clk;

   intf masters[1:0]();

   int   cyc;

   xbar sub
     (.clk,
      .cyc,
      .Masters(masters));

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         masters[0].value <= 2;
         masters[1].value <= 1;
      end
   end

endmodule
