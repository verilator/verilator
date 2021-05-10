// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Rupert Swarbrick.
// SPDX-License-Identifier: CC0-1.0

module t(/*AUTOARG*/
   // Inputs
   value
   );
   input  [1:0] value;

   sub u_sub(.value(value), .out0(), .out1());

endmodule

module sub (input logic [1:0]  value,
            output logic [2:0] out0,
            output logic [2:0] out1);

  always_comb begin
    // This case statement shouldn't cause any warnings. Although the cases overlap (2'b11 matches
    // both 2'b?1 and 2'b1?), the second item matches 2'b10 and the first one doesn't.
    priority casez (value)
      2'b ?1: out0 = 3'd0;
      2'b 1?: out0 = 3'd1;
      default: out0 = 3'd2;
    endcase

    // This case statement *should* cause a warning: the second case is completely covered by the
    // first.
    priority casez (value)
      2'b ?1: out1 = 3'd0;
      2'b ?1: out1 = 3'd1;
      default: out1 = 3'd2;
    endcase

    // This case statement should cause a warning too: the second case and third cases are
    // completely covered by the first. But it should only cause one: like with overlapping cases,
    // we assume that the author messed up the first case, so there's no real benefit to reporting
    // each thing it subsumes.
    priority casez (value)
      2'b ?1: out1 = 3'd0;
      2'b ?1: out1 = 3'd1;
      2'b 11: out1 = 3'd2;
      default: out1 = 3'd3;
    endcase
  end

endmodule
