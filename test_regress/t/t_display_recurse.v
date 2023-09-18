// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer i;
   integer count = 'd0;

   always @(posedge clk) begin
      count <= count + 1;
      if (count == 10) begin
         for(i=0; i<30; i=i+4) begin
            // See issue #4480, verilator may inline getb() which has another display inside it
            $display("%d: %02x%02x%02x%02x", i, getb(i+3), getb(i+2), getb(i+1), getb(i));
         end
      end
      if (count == 11) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   localparam SIZE = 64*1024;
   localparam ADDRW = $clog2(SIZE/4);
   reg [31: 0] ram [(SIZE/4)-1: 0];

   function [7:0] getb;
      input [31:0] address;
      if (address[31:ADDRW+2] != 0) begin
         $display("Address out of range");
      end
      case(address[1:0])
        0: getb = ram[address[ADDRW+1: 2]][8*0+7:8*0];
        1: getb = ram[address[ADDRW+1: 2]][8*1+7:8*1];
        2: getb = ram[address[ADDRW+1: 2]][8*2+7:8*2];
        3: getb = ram[address[ADDRW+1: 2]][8*3+7:8*3];
      endcase
   endfunction

   initial begin
      for (i=0; i<SIZE/4; i=i+1) begin
         ram[i] = {i[15:0], 16'hdead};
      end
   end
endmodule
