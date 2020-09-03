// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface dummy_if ();
   logic signal;

   modport slave
     (output signal);

   modport master
     (input signal);
endinterface: dummy_if

module sub
  (
   input wire  signal_i,
   output wire signal_o,

   dummy_if.master dummy_in,
   dummy_if.slave dummy_out
   );

   assign dummy_in.signal = signal_i;
   assign signal_o = dummy_out.signal;
endmodule


module t (/*AUTOARG*/
   // Outputs
   signal_o,
   // Inputs
   signal_i
   );
   input signal_i;
   output signal_o;

   dummy_if dummy_if ();

   sub sub
     (
      .signal_i(signal_i),
      .signal_o(signal_o),
      .dummy_in(dummy_if),
      .dummy_out(dummy_if)
      );

endmodule
