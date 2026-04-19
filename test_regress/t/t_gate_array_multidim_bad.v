// DESCRIPTION: Verilator: verify multi-dim gate primitive arrays are rejected.
//
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
   wire a, b;
   wire [1:0][1:0] y;
   and g [1:0][1:0] (y, a, b);
endmodule
