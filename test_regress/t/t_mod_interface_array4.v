// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

interface intf ();
   integer index;
endinterface

module t
  (
   clk
   );
   input clk;

   intf ifa1_intf[2:1]();
   intf ifa2_intf[2:1]();
   intf ifb1_intf[1:2]();
   intf ifb2_intf[1:2]();

   int   cyc;

   sub sub
      (
       .clk,
       .cyc,
       .alh(ifa1_intf),
       .ahl(ifa2_intf),
       .blh(ifb1_intf),
       .bhl(ifb2_intf)
       );

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         ifa1_intf[1].index = 'h101;
         ifa1_intf[2].index = 'h102;
         ifa2_intf[1].index = 'h201;
         ifa2_intf[2].index = 'h202;
         ifb1_intf[1].index = 'h301;
         ifb1_intf[2].index = 'h302;
         ifb2_intf[1].index = 'h401;
         ifb2_intf[2].index = 'h402;
      end
   end

endmodule

module sub
  (
   input logic clk,
   input int cyc,
   intf alh[1:2],
   intf ahl[2:1],
   intf blh[1:2],
   intf bhl[2:1]
   );

   always @(posedge clk) begin
      if (cyc == 5) begin
         `checkh(alh[1].index, 'h102);
         `checkh(alh[2].index, 'h101);
         `checkh(ahl[1].index, 'h201);
         `checkh(ahl[2].index, 'h202);
         `checkh(blh[1].index, 'h301);
         `checkh(blh[2].index, 'h302);
         `checkh(bhl[1].index, 'h402);
         `checkh(bhl[2].index, 'h401);
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
