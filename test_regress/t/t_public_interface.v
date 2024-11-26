// DESCRIPTION: Verilator: SystemVerilog interface test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2012 by Iztok Jeras.
// SPDX-License-Identifier: CC0-1.0

interface intf
    (input wire clk,
     input wire rst);
    modport intf_modp (input clk, rst);
endinterface

module sub
/*verilator public_on*/
   (intf.intf_modp intf_port);

   // finish report
   always @ (posedge intf_port.clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
/*verilator public_off*/
endmodule

module t
    (clk);
    input clk   /*verilator public*/ ;
    logic rst;
    intf the_intf (.clk, .rst);
    sub the_sub (.intf_port (the_intf));
endmodule
