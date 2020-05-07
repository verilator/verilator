// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2008 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   string   mystr;
   reg [2:0] cyc; initial cyc = 0;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) if (mystr != "case-1") $stop;
      if (cyc == 4) if (mystr != "case-4") $stop;
      if (cyc == 6) if (mystr != "bad-default") $stop;
      if (cyc == 7) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

   always @ (cyc) begin
      // verilator lint_off CASEINCOMPLETE
      case (cyc)
        3'b000: mystr = "case-0";
        3'b001: mystr = "case-1";
        3'b010: mystr = "case-2";
        3'b100: mystr = "case-4";
        3'b101: mystr = "case-5";
        default: mystr = "bad-default";
      endcase
      //$display("with_case: %d = %s", cyc, mystr);
   end
endmodule
