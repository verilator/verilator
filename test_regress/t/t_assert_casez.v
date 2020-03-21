// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2016 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

   reg [1:0] value;

   initial begin
      value = 2'b00;
      unique casez (value)
        2'b00 : ;
        2'b01 : ;
        2'b1? : ;
      endcase
      value = 2'b11;
      unique casez (value)
        2'b00 : ;
        2'b01 : ;
        2'b1? : ;
      endcase
      unique casez (1'b1)
        default: ;
      endcase
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
