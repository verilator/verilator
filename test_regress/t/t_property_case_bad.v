// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  logic [1:0] sel;

  property p1;
    case (sel)
      default: 1'b1;
      default: 1'b0;
    endcase
  endproperty

  property p2;
    case (sel)
    endcase
  endproperty
endmodule
