// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Conor McCullough.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   reg [63:0]           from = 64'h0706050403020100;
   reg [7:0]            to;
   reg [2:0]            bitn;
   reg [7:0] cyc; initial cyc = 0;

   always @* begin
      to = from[bitn * 8 +: 8];
   end

   always @ (posedge clk) begin
      cyc <= cyc + 8'd1;
      case (cyc)
        8'd00: begin bitn<=3'd0; end
        8'd01: begin bitn<=3'd1; end
        8'd02: begin bitn<=3'd2; end
        8'd03: begin bitn<=3'd3; end
        8'd04: begin bitn<=3'd4; end
        8'd05: begin bitn<=3'd5; end
        8'd06: begin bitn<=3'd6; end
        8'd07: begin bitn<=3'd7; end
        8'd08: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
        default: ;
      endcase
      case (cyc)
        8'd00: ;
        8'd01: begin if (to !== 8'h00) $stop; end
        8'd02: begin if (to !== 8'h01) $stop; end
        8'd03: begin if (to !== 8'h02) $stop; end
        8'd04: begin if (to !== 8'h03) $stop; end
        8'd05: begin if (to !== 8'h04) $stop; end
        8'd06: begin if (to !== 8'h05) $stop; end
        8'd07: begin if (to !== 8'h06) $stop; end
        8'd08: begin if (to !== 8'h07) $stop; end
        default: $stop;
      endcase
   end

endmodule
