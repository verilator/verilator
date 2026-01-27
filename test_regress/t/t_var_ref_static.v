// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Make sure type errors aren't suppressable
// verilator lint_off WIDTH

module t;
   // TODO make this a proper test
   function void crs(const ref static i);
   endfunction
   function void rs(ref static i);
   endfunction
endmodule
