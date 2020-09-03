// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork.
// SPDX-License-Identifier: CC0-1.0

parameter N = 4;
// verilator lint_off LITENDIAN

interface a_if #(parameter PARAM = 0) ();
   logic long_name;
   modport source (output long_name);
   modport sink (input long_name);
endinterface

module intf_source
  (
   input logic [0:N-1] intf_input,
   a_if.source i_intf_source[0:N-1]
   );
   generate
      for (genvar i=0; i < N;i++) begin
	 assign i_intf_source[i].long_name = intf_input[i];
      end
   endgenerate
endmodule

module intf_sink
  (
   output [0:N-1] a_out,
   a_if.sink i_intf_sink[0:N-1]
   );
   generate
      for (genvar i=0; i < N;i++) begin
	 assign a_out[i] = i_intf_sink[i].long_name;
      end
   endgenerate
endmodule

module t
  (
   clk
   );
   input clk;
   logic [0:N-1] a_in;
   logic [0:N-1] a_out;
   logic [0:N-1] ack_out;
   a_if #(.PARAM(1)) tl_intf [0:N-1] ();
   intf_source source(a_in, tl_intf);
   intf_sink   sink(a_out, tl_intf);

   initial a_in = '0;
   always @(posedge clk) begin
      a_in <= a_in + { {N-1 {1'b0}}, 1'b1 };
      ack_out <= ack_out + { {N-1 {1'b0}}, 1'b1 };
      if (ack_out != a_out) begin
         $stop;
      end

      if (& a_in) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
