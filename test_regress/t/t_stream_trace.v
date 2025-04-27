// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (clk);
   input clk;
   integer cyc = 0;

   logic [2:0] cmd_ready;
   logic       cmd_ready_unpack[3];
   logic       cmd_ready_o[3];

   assign cmd_ready = {1'b1, clk, ~clk};
   assign cmd_ready_unpack = {<<{cmd_ready}};
   assign cmd_ready_o = cmd_ready_unpack;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      if (cyc == 5) begin
         $write("*-* All Finished *-*\n");
         $finish;
      end
   end
endmodule
