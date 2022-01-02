// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

module t(/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   sub sub();

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      // procedural var sub.subvar
      if (cyc == 50) begin
         `checkh(sub.subvar, 32'h666);
         force sub.subvar = 32'hffff;
      end
      else if (cyc == 51) begin
         `checkh(sub.subvar, 32'hffff);
         sub.subvar = 32'h543;  // Ignored as still forced
      end
      else if (cyc == 52) begin
         `checkh(sub.subvar, 32'hffff);
      end
      else if (cyc == 53) begin
         release sub.subvar;
      end
      else if (cyc == 54) begin
         `checkh(sub.subvar, 32'hffff);  // Retains value until next procedural change
         sub.subvar = 32'h544;
      end
      else if (cyc == 56) begin
         `checkh(sub.subvar, 32'h544);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module sub;
   int subvar;
   initial subvar = 32'h666;
endmodule
