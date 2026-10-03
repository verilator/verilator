// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Greg Davill
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (  /*AUTOARG*/);

  // Test: 2D array localparam with pattern initialization
  localparam logic [31:0] MATRIX[2][3] = '{'{32'hA0, 32'hA1, 32'hA2}, '{32'hB0, 32'hB1, 32'hB2}};

  // Deriving a localparam from a 2D array element
  localparam logic [31:0] DERIVED_A0 = MATRIX[0][0];
  localparam logic [31:0] DERIVED_B2 = MATRIX[1][2];

  // Use derived values as sub-module parameters to force elaboration-time resolution
  sub #(.VAL(MATRIX[0][1])) u_sub ();

  initial begin
    `checkh(DERIVED_A0, 32'hA0);
    `checkh(DERIVED_B2, 32'hB2);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module sub #(
    parameter logic [31:0] VAL = 0
) ();
  initial begin
    if (VAL !== 32'hA1) begin
      $display("%%Error: sub VAL='h%x expected 'hA1", VAL);
      $stop;
    end
  end
endmodule
