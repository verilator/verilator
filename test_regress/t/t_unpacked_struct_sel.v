// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

typedef struct {
   bit [3:0] byte_en;
} my_struct;

module t;
   initial begin
      my_struct ms;
      ms.byte_en[0] = 1;
      if (ms.byte_en[0] != 1) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
