// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Yossi Nivin
// SPDX-License-Identifier: CC0-1.0

module t;

   integer count;
   assign count = $countbits(32'h123456, '0, '1, 'x, 'z);

endmodule
