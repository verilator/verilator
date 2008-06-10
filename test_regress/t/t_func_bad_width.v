// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;

   reg [3:0] out;
   reg [38:0] in;
   initial begin
      in = 39'h0;
      out = MUX (in);
      $write("bad widths %x", out);
   end

   function [31:0] MUX;
      input [39:0] XX ;
      begin
         MUX = XX[39:8];
      end
   endfunction
endmodule
