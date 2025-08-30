// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

interface QBus(input logic k);
   logic data;
endinterface

class cls;
    virtual QBus vif1;

    function foo(virtual QBus vif2);
        vif2.data = 1;
    endfunction
endclass

module t (/*AUTOARG*/);

   cls bar;

   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
