// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module gymhnulbvj (in5, clock_10, clock_12, out18);

   input wire [23:22] in5;
   wire [29:1] wire_4;
   reg reg_35;
   output wire out18;
   input wire clock_10;
   input wire clock_12;

   // verilator lint_off WIDTH
   assign wire_4 = ~ in5[22];
   assign out18 = reg_35 ? 0 : !(!(~(wire_4[6:5] | 8'hc6)));
   // verilator lint_on WIDTH

   always @(posedge clock_10 or posedge clock_12) begin
      if (clock_12) begin
         reg_35 <= 0;
      end
      else begin
         // verilator lint_off WIDTH
         reg_35 <= wire_4;
         // verilator lint_on WIDTH
      end
   end
endmodule

module t;
   reg [23:22] in5;
   reg clock_10 = 0;
   reg clock_12 = 0;
   wire out18;

   gymhnulbvj uut (
                   .in5(in5),
                   .clock_10(clock_10),
                   .clock_12(clock_12),
                   .out18(out18)
                   );

   initial begin
      $monitor("[%0t] in5=%d clock_10=%d clock_12=%d out18=%d", $time, in5, clock_10, clock_12, out18);

      in5 = 2'b00;
      #5 clock_12 = 1;
      #5 clock_12 = 0;

      #5 clock_10 = 1;
      #5 clock_10 = 0;

      #10;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
