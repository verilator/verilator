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

   intf ifa1_intf[4:1]();
   intf ifa2_intf[4:1]();
   intf ifb1_intf[1:4]();
   intf ifb2_intf[1:4]();

   int   cyc;

   sub sub0
      (
       .n(0),
       .clk,
       .cyc,
       .alh(ifa1_intf[2:1]),
       .ahl(ifa2_intf[2:1]),
       .blh(ifb1_intf[1:2]),
       .bhl(ifb2_intf[1:2])
       );

   sub sub1
      (
       .n(1),
       .clk,
       .cyc,
       .alh(ifa1_intf[4:3]),
       .ahl(ifa2_intf[4:3]),
       .blh(ifb1_intf[3:4]),
       .bhl(ifb2_intf[3:4])
       );

`ifndef verilator // Backwards slicing not supported
   sub sub2
      (
       .n(2),
       .clk,
       .cyc,
       .alh(ifa1_intf[1:2]),  // backwards vs decl
       .ahl(ifa2_intf[1:2]),  // backwards vs decl
       .blh(ifb1_intf[2:1]),  // backwards vs decl
       .bhl(ifb2_intf[2:1])  // backwards vs decl
       );

   sub sub3
      (
       .n(3),
       .clk,
       .cyc,
       .alh(ifa1_intf[3:4]),  // backwards vs decl
       .ahl(ifa2_intf[3:4]),  // backwards vs decl
       .blh(ifb1_intf[4:3]),  // backwards vs decl
       .bhl(ifb2_intf[4:3])  // backwards vs decl
       );
`endif

   always @(posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
         ifa1_intf[1].index = 'h101;
         ifa1_intf[2].index = 'h102;
         ifa1_intf[3].index = 'h103;
         ifa1_intf[4].index = 'h104;
         ifa2_intf[1].index = 'h201;
         ifa2_intf[2].index = 'h202;
         ifa2_intf[3].index = 'h203;
         ifa2_intf[4].index = 'h204;
         ifb1_intf[1].index = 'h301;
         ifb1_intf[2].index = 'h302;
         ifb1_intf[3].index = 'h303;
         ifb1_intf[4].index = 'h304;
         ifb2_intf[1].index = 'h401;
         ifb2_intf[2].index = 'h402;
         ifb2_intf[3].index = 'h403;
         ifb2_intf[4].index = 'h404;
      end
   end

endmodule

module sub
  (
   input logic clk,
   input int cyc,
   input int n,
   intf alh[1:2],
   intf ahl[2:1],
   intf blh[1:2],
   intf bhl[2:1]
   );

   always @(posedge clk) begin

      if (cyc == 5) begin
         if (n == 0) begin
            `checkh(alh[1].index, 'h102);
            `checkh(alh[2].index, 'h101);
            `checkh(ahl[1].index, 'h201);
            `checkh(ahl[2].index, 'h202);
            `checkh(blh[1].index, 'h301);
            `checkh(blh[2].index, 'h302);
            `checkh(bhl[1].index, 'h402);
            `checkh(bhl[2].index, 'h401);
         end
         else if (n == 1) begin
            `checkh(alh[1].index, 'h104);
            `checkh(alh[2].index, 'h103);
            `checkh(ahl[1].index, 'h203);
            `checkh(ahl[2].index, 'h204);
            `checkh(blh[1].index, 'h303);
            `checkh(blh[2].index, 'h304);
            `checkh(bhl[1].index, 'h404);
            `checkh(bhl[2].index, 'h403);
         end
         else if (n == 2) begin
            `checkh(alh[1].index, 'h101);
            `checkh(alh[2].index, 'h102);
            `checkh(ahl[1].index, 'h202);
            `checkh(ahl[2].index, 'h201);
            `checkh(blh[1].index, 'h302);
            `checkh(blh[2].index, 'h301);
            `checkh(bhl[1].index, 'h401);
            `checkh(bhl[2].index, 'h402);
         end
         else if (n == 3) begin
            `checkh(alh[1].index, 'h103);
            `checkh(alh[2].index, 'h104);
            `checkh(ahl[1].index, 'h204);
            `checkh(ahl[2].index, 'h203);
            `checkh(blh[1].index, 'h304);
            `checkh(blh[2].index, 'h303);
            `checkh(bhl[1].index, 'h403);
            `checkh(bhl[2].index, 'h404);
         end
      end
      if (cyc == 9 && n == 0) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end

endmodule
