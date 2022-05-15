// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   reg start = 0;
   reg [31:0] count;
   reg [31:0] runner = 0;

   always @ (posedge start) count = 0;
   always @ (posedge start) runner = 3;

   always @ (runner) begin
      if (runner > 0) begin
         $display("count=%d  runner=%d",count, runner);
         count = count + 1;
         runner = runner - 1;;
      end
   end

   reg [7:0] cyc = 0;
   always @ (posedge clk) begin
      cyc <= cyc + 8'd1;
      case (cyc)
        8'd00: start <= 1'b0;
        8'd01: start <= 1'b1;
        8'd02: begin
           $display("Final count=%d", count);
           if (count!=32'h3) $stop;
        end
        default: begin
           $write("*-* All Finished *-*\n");
           $finish;
        end
      endcase
   end
endmodule
