// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   // verilator lint_off WIDTH
   typedef enum logic[2:0] {P=0, W=1'b1, E, N, S} Dirs;

   typedef enum integer {UP=0, UW=1'b1} UNSIZED;
   // verilator lint_on WIDTH

   localparam LEN = 3;
   localparam COL = 4;

   localparam [59:0] SEQ = {LEN'(N), LEN'(E), LEN'(W), LEN'(P)
                            ,LEN'(S), LEN'(E), LEN'(W), LEN'(P)
                            ,LEN'(S), LEN'(N), LEN'(W), LEN'(P)
                            ,LEN'(S), LEN'(N), LEN'(E), LEN'(P)
                            ,LEN'(S), LEN'(N), LEN'(E), LEN'(W)};

   bit [59:0] SE2 = {N, E, W, P
                     ,S, E, W, P
                     ,S, N, W, P
                     ,S, N, E, P
                     ,S, N, E, W};

   initial begin
      if (SEQ != 60'o32104210431043204321) $stop;
      if (SE2 != 60'o32104210431043204321) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
