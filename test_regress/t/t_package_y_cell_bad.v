// DESCRIPTION: Verilator: Instancing a -y package is not a module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  import ypkg::*;
  // Package, not a module; ypkg.v must not be parsed again
  ypkg u_ypkg ();
endmodule
