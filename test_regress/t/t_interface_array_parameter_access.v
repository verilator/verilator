// DESCRIPTION: Verilator: Get parameter from array of interfaces
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2024 by Todd Strader
// SPDX-License-Identifier: CC0-1.0

interface intf
  #(parameter int FOO = 4)
    (input wire clk,
     input wire rst);
    modport modp (input  clk, rst);
endinterface

module sub (intf.modp the_intf_port [4]);
    localparam int intf_foo = the_intf_port[0].FOO;

    initial begin
        if (intf_foo != 4) $stop;
    end
endmodule

module t (
    clk
);
    logic rst;
    input clk;

    intf the_intf [4] (.*);

    sub
    the_sub (
        .the_intf_port   (the_intf)
    );

   always @(posedge clk) begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
