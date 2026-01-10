// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off WIDTH

module pipe_id_match #(
    parameter type ID_T = logic [4:0],
    parameter ID_T STAGE_IDS[3:0][1:0] = '{default: 1}
);
  generate
    $info("%m %s:%0d: 4=%0d 2=%0d STAGE_IDS=%p", "test.sv", 25, 4, 2, STAGE_IDS);
  endgenerate
endmodule

module t #(
    parameter type ID_T = logic [4:0]
);

  localparam ID_T STAGE_IDS[3:0][1:0] = '{default: 5'b1};

  pipe_id_match #(
      .ID_T(ID_T),
      .STAGE_IDS(STAGE_IDS)
  ) pipe (
      .*
  );

  initial $finish;

endmodule
