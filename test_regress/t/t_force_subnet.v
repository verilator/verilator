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

   tri        logic [7:0] subnet;
   sub1 sub1(.*);
   sub2 sub2(.*);

   // Test loop
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         `checkh(subnet, 8'h11);
         force sub1.subnet = 8'h00;  // sub1.subnet same as subnet
      end
      else if (cyc == 11) begin
         `checkh(subnet, 8'h00);
         force subnet = 8'h10;  // sub1.subnet same as subnet
      end
      else if (cyc == 12) begin
         `checkh(subnet, 8'h10);
         release subnet;  // sub1.subnet same as subnet
      end
      else if (cyc == 13) begin
         `checkh(subnet, 8'h11);
      end
      //
      else if (cyc == 99) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule

module sub1(inout logic [7:0] subnet);
   assign subnet = 8'hz1;
endmodule

module sub2(inout logic [7:0] subnet);
   assign subnet = 8'h1z;
endmodule

