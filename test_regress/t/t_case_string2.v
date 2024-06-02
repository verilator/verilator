// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;

function automatic string broken_case(input string some_string);
    case(some_string)
        "alpha": return "alpha";
        default: return "beta";
    endcase
endfunction

   initial begin
      $display(broken_case("gamma"));
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
