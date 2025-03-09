// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2021 by Ryszard Rozak.
// SPDX-License-Identifier: CC0-1.0

module dut(output int x);
   parameter int P [5];
   assign x = P[2];
endmodule

module t();
   int o;
   dut #(.P('{1, 2, 3, 4, 5})) u_dut(.x(o));

   initial begin
      if (o !== 3) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
