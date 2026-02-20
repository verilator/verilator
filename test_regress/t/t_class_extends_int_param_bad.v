// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;

   class Bar #(type T=int) extends T;
   endclass

   initial begin
      Bar#() bar;
      $stop;
   end
endmodule
