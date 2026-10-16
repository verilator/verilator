// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

typedef int unsigned one_t[1];

module sub #(
    parameter int unsigned VAL[2] = '{1, 2},
    parameter one_t ONE = '{1}
) ();
endmodule

module t;
  localparam one_t NINE = '{9};

  sub sub12 ();
  sub #(.VAL('{3, 4})) sub34 ();
  // Unpacked array concatenations (#6686)
  sub #(
      .VAL({32'd5, 32'd6}),
      .ONE({NINE[0]})
  ) sub56 ();

  initial begin
    if (sub12.VAL[0] != 1) $stop;
    if (sub12.VAL[1] != 2) $stop;
    if (sub34.VAL[0] != 3) $stop;
    if (sub34.VAL[1] != 4) $stop;
    if (sub56.VAL[0] != 5) $stop;
    if (sub56.VAL[1] != 6) $stop;
    if (sub56.ONE[0] != 9) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
