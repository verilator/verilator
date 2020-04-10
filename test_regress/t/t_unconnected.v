// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   wire o_n;
   wire o_0;
   wire o_1;

   // verilator lint_off PINMISSING
   sub_0 sub_0(.o_0);
   sub_1 sub_1(.o_1);
   sub_n sub_n(.o_n);
   // verilator lint_on PINMISSING

   always @ (posedge clk) begin
      if (o_0 !== 1'b0) $stop;
      if (o_1 !== 1'b1) $stop;
      //4-state if (o_n !== 1'bz) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule

`unconnected_drive pull0
module sub_0 (input i, output wire o_0);
   assign o_0 = i;
endmodule

`unconnected_drive pull1
module sub_1 (input i, output wire o_1);
   assign o_1 = i;
endmodule

`nounconnected_drive
module sub_n (input i, output wire o_n);
   assign o_n = i;
endmodule
