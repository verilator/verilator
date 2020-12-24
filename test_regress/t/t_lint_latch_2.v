// DESCRIPTION: Verilator: Verilog Test module for Issue#1609
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Julien Margetts.

module t (/*AUTOARG*/ i, o);

   input      [1:0] i;
   output reg [1:0] o;

    // This should not detect a latch as all options are covered
   always @* begin
     if      (i==2'b00) o = 2'b11;
     else if (i==2'b01) o = 2'b10;
     else if (i==2'b10) o = 2'b01;
     else if (i==2'b11) o = 2'b00;
     else               o = 2'b00; // Without this else a latch is (falsely) detected
   end

endmodule
