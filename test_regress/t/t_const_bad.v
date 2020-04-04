// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/);

   initial begin
      if (32'hxxxxxxxx !== 'hx) $stop;
      if (32'hzzzzzzzz !== 'hz) $stop;
      if (32'h???????? !== 'h?) $stop;
      if (68'hx_xxxxxxxx_xxxxxxxx !== 'dX) $stop;
      if (68'hz_zzzzzzzz_zzzzzzzz !== 'dZ) $stop;
      if (68'h?_????????_???????? !== 'd?) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
