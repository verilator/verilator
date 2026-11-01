// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package P0;
  integer y;
endpackage

package P1;
  integer x;
  integer y;
endpackage

package P2;
  import P1::x;
  export P1::y;  // <--- Error: P1::y has not been imported
endpackage

package P3;
  import P0::y;
  export P1::y;  // <--- Error: P1::y has not been imported, P0::y was
endpackage

package P4;
  import P2::*;
  export P2::x;  // <--- Error: P2::x was not exported from P2, so can't be imported
endpackage

module t;
endmodule
