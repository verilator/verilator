// DESCRIPTION::Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

package pkg;
  int unsigned id = 0;

  function int unsigned func();
    int unsigned local_id;
    local_id  = id + 1;
    id = local_id;
    return local_id;
  endfunction : func
endpackage

module t(/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;
  import pkg::*;
  int unsigned func_id = func();

  always @ (posedge clk) begin
    $display(id);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
