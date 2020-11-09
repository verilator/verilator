// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   logic in1 = 1;
   logic [1:0] in2 = 2'b11;
   logic [31:0] out;
   logic [7:0]  ones = 8'b11111111;
   logic [9:0]  ones10 = 10'b1111111111;

   typedef logic [7:0] data_t;

   typedef logic [9:0] ten_t;
   ten_t out10;

   // verilator lint_off WIDTH
   initial begin
      in1 = 1;
      in2 = 0;
      out = data_t'(in1 << in2);
      if (out != 8'b1) $stop;

      in2 = 1;
      out = data_t'(in1 << in2);
      if (out != 8'b10) $stop;

      in2 = 2;
      out = data_t'(in1 << in2);
      if (out != 8'b100) $stop;

      in2 = 3;
      out = data_t'(in1 << in2);
      if (out != 8'b1000) $stop;

      // Check upper bits get cleared when cast
      in2 = 3;
      out = data_t'(ones << in2);
      if (out != 8'b11111000) $stop;

      in2 = 3;
      out = data_t'(ones10 << in2);
      if (out != 8'b11111000) $stop;

      // bug2597
      out = data_t'(10'h208 >> 2);
      if (out != 8'h82) $stop;

      out = data_t'(10'h208 >> 2);
      if (out != 8'h82) $stop;

      out = data_t'('h208 >> 2);
      if (out != 8'h82) $stop;

      out10 = ten_t'('h404 >> 2);
      if (out10 != 10'h101) $stop;

      $write("*-* All Finished *-*\n");
      $finish();
   end
endmodule
