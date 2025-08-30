// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

typedef int Int_T;

module t;
  initial begin
    Int_T value1 = 7;
    int value2 = 13;
    real r;
    if (type(value1) != type(value2)) $stop;
    if (type(value1 + value2) != type(value2 + 18)) $stop;
    case (type(value1))
      type(value2): ;
      type(r): $stop;
      type(chandle): $stop;
      type(logic): $stop;
      default: $stop;
    endcase
    case (type(value1 + value2 + 13))
      type(type(value2 + 18 - 40)): ;
      type(r): $stop;
      type(chandle): $stop;
      default: $stop;
    endcase
    if (type(value1) == type(value2) && type(value1 + value2) == type(value2 + 18)) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end else begin
      $stop;
    end
  end
endmodule
