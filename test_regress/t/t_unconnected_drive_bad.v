// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // verilator lint_off PINMISSING
  sub_p1_real sub_p1_real ();
  sub_p0_real sub_p0_real ();
  sub_p1_array sub_p1_array ();
  // verilator lint_on PINMISSING
endmodule

`unconnected_drive pull1
module sub_p1_real (
    input real i
);
endmodule

`unconnected_drive pull0
module sub_p0_real (
    input real i
);
endmodule

`unconnected_drive pull1
module sub_p1_array (
    input [3:0] i [2]
);
endmodule

`nounconnected_drive
