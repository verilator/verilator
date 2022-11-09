// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
      clk
   );

   input clk;

   function void infinite_loop;
      do begin
         continue;
      end
      while (1);
   endfunction

   always @(posedge clk) begin
      infinite_loop();
      $stop;
   end
endmodule
