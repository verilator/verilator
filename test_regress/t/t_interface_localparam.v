// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2023 by Justin Thiel.
// SPDX-License-Identifier: CC0-1.0

/// Test for bug3858

interface SimpleIntf
#(
   parameter int symbolsPerBeat = 16
)
();

   // This value is calculated incorrectly for other instances of
   // this interface when it is accessed via the HDL for any other
   // instance of this interface
   localparam int symbolsPerBeatDivBy2  = symbolsPerBeat/2;

   localparam bit mismatch = (symbolsPerBeat != (2*symbolsPerBeatDivBy2) );

   initial begin
      $write("%m: symbolsPerBeat %0d, symbolsPerBeatDivBy2 %0d, mismatch %0d\n",
             symbolsPerBeat, symbolsPerBeatDivBy2, mismatch);
      if (mismatch) $stop;
   end

endinterface

module Core(
   SimpleIntf intf
);

   // NOTE: When this line is commented out the test will pass
   localparam intf_symbolsPerBeatDivBy2 = intf.symbolsPerBeatDivBy2;

   localparam int core_intf_symbolsPerBeat = 64;
   SimpleIntf #(.symbolsPerBeat(core_intf_symbolsPerBeat)) core_intf ();

endmodule

module t();

   SimpleIntf intf();

   Core theCore (.intf);

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
