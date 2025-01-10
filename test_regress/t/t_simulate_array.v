// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

function integer fun;
integer array[0:0];
begin
    array[0] = 10;
    fun = array[0];
end
endfunction

module test ();
begin
    localparam something = fun();
    initial begin
      if (something !== 10) $stop;
      $write("*-* All Finished *-*\n");
      $finish;
    end
end
endmodule
