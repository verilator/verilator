// DESCRIPTION: Verilator: Importing a -y module does not re-read its file
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  ymod u_ymod ();
  // Module, not a package; ymod.v must not be parsed again
  import ymod::*;
endmodule
