// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  import "DPI-C" function void dpii_open(input byte h[][]);
  import "DPI-C" function void dpii_open_packed(input bit [] h[][]);
  import "DPI-C" function void dpii_open_int(input int h[]);

  initial begin
    // Dynamic array or queue other than as the first dimension
    byte fixed_dyn[3][];
    byte dyn_queue[][$];
    bit [7:0] bits_fixed_dyn[3][];
    int ints[2];
    dpii_open(fixed_dyn);
    dpii_open(dyn_queue);
    dpii_open_packed(bits_fixed_dyn);
    // Empty queue
    dpii_open({});
    // Streaming concatenation (IEEE 1800-2023 11.4.14)
    dpii_open_int({>>{ints}});
  end
endmodule
