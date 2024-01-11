// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Justin Thiel.
// SPDX-License-Identifier: CC0-1.0

interface SimpleIntf
#(
   parameter int val = 28
)
();

   // This value is calculated incorrectly for other instances of
   // this interface when it is accessed via the HDL for any other
   // instance of this interface
   localparam int valDiv2  = val/2;
   localparam int valDiv4  = valDiv2/2;

   localparam bit mismatch2 = (val != (2*valDiv2) );
   localparam bit mismatch4 = (val != (4*valDiv4) );

   initial begin
      $write("%m: val %0d, valDiv2 %0d, mismatch2 %0d\n",
             val, valDiv2, mismatch2);
      $write("%m: val %0d, valDiv4 %0d, mismatch4 %0d\n",
             val, valDiv4, mismatch2);
      if (mismatch2) $stop;
      if (mismatch4) $stop;
   end

endinterface

module Core(
   SimpleIntf intf
);

   // this will constify and valDiv2 will have the default value
   localparam valDiv4Upper = intf.valDiv2;

   SimpleIntf #(.val(68)) core_intf ();

   initial begin
      if (intf.valDiv2 != valDiv4Upper) begin
         $display("%%Error: param = %0d", intf.valDiv2);
      end
   end
endmodule

module t();

   SimpleIntf intf();

   Core theCore (.intf);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
