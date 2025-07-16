// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  specify
    specparam tdevice_PU = 3e8;
    specparam Tdelay11 = 1.1;
    // verilator lint_off MINTYPMAXDLY
    specparam Tmintypmax = 1.0:1.1:1.2;
    specparam PATHPULSE$a$b = (3.0:3.1:3.2, 4.0:4.1:4.2);
    specparam randomize = 1;  // Special parser corner-case
  endspecify

  // Support in other simulators is limited for module specparams
  specparam Tmod34 = 3.4, Tmod35 = 3.5;  // IEEE 6.20.5 allowed in body
  // Support in other simulators is limited for ranged specparams
  specparam [5:2] Tranged = 4'b1011;

  localparam real PATHPULSE$normal$var = 6.78;

  reg PoweredUp;
  wire DelayIn, DelayOut;

  assign #tdevice_PU DelayOut = DelayIn;

  initial begin
    PoweredUp = 1'b0;
    #tdevice_PU PoweredUp = 1'b1;
    if (Tdelay11 != 1.1) $stop;
`ifdef VERILATOR
    if (Tmintypmax != 1.1) $stop;
    if (PATHPULSE$a$b != 3.1) $stop;
`endif
    if (Tranged != 4'b1011) $stop;
    if (Tmod34 != 3.4) $stop;
    if (Tmod35 != 3.5) $stop;
    if (PATHPULSE$normal$var != 6.78) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
