// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Greg Davill
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (  /*AUTOARG*/);

  // Test: 3D array localparam with pattern initialization
  localparam logic [31:0] CUBE[2][2][2] = '{
      '{'{32'h00, 32'h01}, '{32'h10, 32'h11}},
      '{'{32'h20, 32'h21}, '{32'h30, 32'h31}}
  };

  // Deriving a localparam from a 3D array element
  localparam logic [31:0] CUBE_VAL = CUBE[1][0][1];

  initial begin
    `checkh(CUBE_VAL, 32'h21);
    `checkh(CUBE[0][0][0], 32'h00);
    `checkh(CUBE[0][1][1], 32'h11);
    `checkh(CUBE[1][1][0], 32'h30);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
