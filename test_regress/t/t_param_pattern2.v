// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2021 Ryszard Rozak
// SPDX-License-Identifier: CC0-1.0

module dut
  #(parameter int P [5])
  (output int x);
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
