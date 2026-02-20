// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Iztok Jeras
// SPDX-License-Identifier: CC0-1.0

interface intf();

   function automatic string get_scope;
      string the_scope = $sformatf("%m");
      return the_scope;
   endfunction

   initial $display(get_scope());
endinterface

module t (/*AUTOARG*/
   // Inputs
   clk
   );

   input clk;

   // finish report
   always @ (posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end

   intf the_intf();

endmodule
