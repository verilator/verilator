// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   sub #(.WIDTH(4)) sub4();
   sub #(.WIDTH(8)) sub8();

   logic [3:0] out4;
   logic [7:0] out8;

   initial begin
      out4 = sub4.orer(4'b1000);
      out8 = sub8.orer(8'b10000000);
      if (out4 != 4'b1011) $stop;
      if (out8 != 8'b10111111) $stop;
      out4 = sub4.orer2(4'b1000);
      out8 = sub8.orer2(8'b10000000);
      if (out4 != 4'b1001) $stop;
      if (out8 != 8'b10011111) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule


module sub;
   parameter WIDTH = 1;

   function [WIDTH-1:0] orer;
      input [WIDTH-1:0] in;
      // IEEE provices no way to override this parameter, basically it's a localparam
      parameter MASK_W = WIDTH - 2;
      localparam [MASK_W-1:0] MASK = '1;
      // verilator lint_off WIDTH
      return in | MASK;
      // verilator lint_on WIDTH
   endfunction

   function [WIDTH-1:0] orer2;
      input [WIDTH-1:0] in;
      // Same param names as other function to check we disambiguate
      // IEEE provices no way to override this parameter, basically it's a localparam
      parameter MASK_W = WIDTH - 3;
      localparam [MASK_W-1:0] MASK = '1;
      // verilator lint_off WIDTH
      return in | MASK;
      // verilator lint_on WIDTH
   endfunction
endmodule
