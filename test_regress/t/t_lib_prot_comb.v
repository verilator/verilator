// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Yutetsu TAKATSUKASA.
// SPDX-License-Identifier: CC0-1.0

`ifdef PROCESS_TOP
`define CHECK if (out0 != (in0 ^ in1) || out1 != (in0 | in1) || out2 != (in0 & in1)) begin \
   $display("Mismatch in0:%b in1:%b out0:%b out1:%b out2:%b", in0, in1, out0, out1, out2); \
   $stop; \
   end

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;


   logic in0, in1;
   logic out0, out1, out2;
   logic [31:0] count = 0;
   // actually XOR and OR and AND
   secret i_secret(.in0(in0), .in1(in1), .out0(out0), .out1(out1), .out2(out2));

   always @(posedge clk) begin
      count <= count + 32'd1;
      if (count == 32'd1) begin
         in0 <= 1'b0;
         in1 <= 1'b0;
      end else if (count == 32'd2) begin
         `CHECK
         in0 <= 1'b1;
         in1 <= 1'b0;
      end else if (count == 32'd3) begin
         `CHECK
         in0 <= 1'b0;
         in1 <= 1'b1;
      end else if (count == 32'd4) begin
         `CHECK
         in0 <= 1'b1;
         in1 <= 1'b1;
      end else if (count == 32'd5) begin
         `CHECK
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

`else
module secret(input in0, input in1, output out0, output out1, output out2);
   assign out0 = in0 ^ in1;
   assign out1 = in0 | in1;
   assign out2 = in0 & in1;
endmodule
`endif
