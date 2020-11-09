// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Thierry Tambe.
// SPDX-License-Identifier: CC0-1.0

module t (
   input logic  clk,
   output logic HRESETn
   );

   int          primsig[3];

   ahb_slave_intf iinst[3] (primsig[2:0]);

   sub sub01 [2] (.clk, .infc(iinst[0:1]));
   sub sub2 (.clk, .infc(iinst[2]));

   initial begin
      primsig[0] = 30;
      primsig[1] = 31;
      primsig[2] = 32;
      iinst[0].data = 10;
      iinst[1].data = 11;
      iinst[2].data = 12;
   end

   int cyc = 0;
   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 10) begin
         if (iinst[0].primsig != 30) $stop;
         if (iinst[1].primsig != 31) $stop;
         if (iinst[2].primsig != 32) $stop;
         if (iinst[0].data != 10) $stop;
         if (iinst[1].data != 11) $stop;
         if (iinst[2].data != 12) $stop;
         if (sub01[0].internal != 10) $stop;
         if (sub01[1].internal != 11) $stop;
         if (sub2.internal != 12) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module sub
(
       input logic clk,
       ahb_slave_intf infc
       );

   int internal;

   always_comb internal = infc.data;

endmodule

interface ahb_slave_intf
   (
    input int primsig
    );

   int          data;

endinterface
