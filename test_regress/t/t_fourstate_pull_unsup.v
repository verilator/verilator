// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    inout [7:0] iolines
);
  pullup d_0_pup (iolines[0]);
  pullup d_1_pup (iolines[1]);
  pulldown d_2_pdown (iolines[2]);
  pulldown d_3_pdown (iolines[3]);
endmodule
