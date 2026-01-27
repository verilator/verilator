// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0
//

class Cls;
  task t;
    i.super.i = 1;  // <--- BAD: cannot dot a reference to get super
  endtask
endclass
