// DESCRIPTION: Verilator: Verilog Test module
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Todd Strader
// SPDX-License-Identifier: CC0-1.0

module secret_impl (
                    input  a,
                    input  oe,
                    inout  z,
                    output y);

   assign z = oe ? a : 1'bz;
   assign y = z;

endmodule
