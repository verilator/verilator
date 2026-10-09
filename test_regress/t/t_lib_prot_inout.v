// DESCRIPTION: Verilator: Protected library inout port
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2019 Todd Strader
// SPDX-License-Identifier: CC0-1.0

module secret_impl (
    input a,
    input oe,
    inout z_secret,
    output y
);

  assign z_secret = oe ? a : 1'bz;
  assign y = z_secret;

endmodule
