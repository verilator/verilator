// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module sub
    #(
        parameter int unsigned VAL[2] = '{1, 2}
    )
    ();
endmodule

module t;
   sub sub12 ();
   sub #(.VAL ( '{3, 4} )) sub34 ();

   initial begin
      if (sub12.VAL[0] != 1) $stop;
      if (sub12.VAL[1] != 2) $stop;
      if (sub34.VAL[0] != 3) $stop;
      if (sub34.VAL[1] != 4) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
