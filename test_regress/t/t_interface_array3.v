// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

interface my_ifc ();
   logic sig;
   modport master ( output sig );
   modport slave ( input sig );
endinterface

package my_pkg;
   typedef virtual my_ifc my_vif;
   function void my_func;
      input my_vif in_vif;
      begin
         in_vif.sig = 1'b1;
      end
   endfunction
endpackage

module dut (input logic clk, my_ifc.slave sif[2]);
   generate
      genvar i;
      for (i=0; i<2; i++) begin
         always_ff @( posedge clk ) begin
            if (sif[i].sig == 1'b1) $display("Hello World %0d", i);
         end
      end
   endgenerate
endmodule

module t;
   import my_pkg::*;

   logic clk;
   my_ifc sif[2] ();

   dut DUT (.*);

   initial begin
      clk = 0;
      forever #(5) clk = ~clk;
   end

   initial begin
      repeat (4) @(posedge clk);
      my_func(sif[0]);
      my_func(sif[1]);
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
