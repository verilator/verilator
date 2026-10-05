// DESCRIPTION: Verilator: Reject class and typedef with the same $unit name
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

class CollidingType;
endclass

typedef int CollidingType;

module t;
endmodule
