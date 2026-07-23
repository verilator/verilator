// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

class Cls #(
    type PARAMA,
    type PARAMB
);
endclass

module t;

  // Missing type params
  Cls c;

endmodule
