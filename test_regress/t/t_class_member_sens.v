// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
    // Inputs
    clk
    );
    input clk;

    class EventClass;
        event e;
    endclass

    EventClass ec = new;
    int cyc = 0;

    always @ec.e ec = new;

    always @(posedge clk) begin
       cyc <= cyc + 1;
       if (cyc == 1) ->ec.e;
       else if (cyc == 2) begin
          $write("*-* All Finished *-*\n");
          $finish;
       end
   end
endmodule
