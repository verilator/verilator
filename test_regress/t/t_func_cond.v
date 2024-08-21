// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  function automatic logic func_with_cond(logic x);
    return x ? func_with_case(0) : 0;
  endfunction

  function automatic logic func_with_case(logic x);
    logic result = 1'b0;
    unique case (1'b0)
      1'b0: result = x;
      1'b1: result = x;
    endcase
    return result;
  endfunction

  initial begin
    if (func_with_cond(0)) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
