// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/);

   logic in1 = 1;
   logic [1:0] in2 = 2'b11;
   logic [31:0] out;

   typedef logic [7:0] data_t;

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

      $write("*-* All Finished *-*\n");
      $finish();
   end
endmodule
