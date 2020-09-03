// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2020 by Stefan Wallentowitz.
// SPDX-License-Identifier: CC0-1.0

module t();
  logic din [0:15];

  array_test array_test_inst(.din(din));

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module array_test(
    input din [0:15]
);
endmodule
