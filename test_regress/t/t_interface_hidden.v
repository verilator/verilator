// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;
   integer cyc=1;

   ifc ifc();  // Cell name hides interface's name
   assign ifc.ifi = 55;

   sub sub (.isub(ifc));  // Cell name hides module's name

   int om;

   mod_or_type mot (.*);

   hides_with_type hides_type();
   hides_with_decl hides_decl();

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 20) begin
         if (om != 22) $stop;
         if (mot.LOCAL != 22) $stop;
         if (ifc.ifo != 55) $stop;
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule

module sub
  (
   ifc isub
   );
   always @* begin
      isub.ifo = isub.ifi;
   end
endmodule

module mod_or_type(output int om);
   localparam LOCAL = 22;
   initial om = 22;
endmodule

module hides_with_type();
   typedef int ifc;  // Hides interface
   typedef int mod_or_type;  // Hides module

   ifc /*=int*/ hides_ifc;
   mod_or_type /*=int*/ hides_mod;

   initial hides_ifc = 33;
   initial hides_mod = 44;
endmodule

module hides_with_decl();
   int ifc;  // Hides interface
   int mod_or_type;  // Hides module

   initial ifc = 66;
   initial mod_or_type = 77;
endmodule

interface ifc;
   localparam LOCAL = 12;
   int ifi;
   int ifo;
endinterface
