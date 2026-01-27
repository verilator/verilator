// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t;
  wire sig;
  foo foo(sig);

  initial #1 begin
    $write("*-* All Finished *-*\n");
    $finish();
  end
endmodule

module foo(inout sig);
  reg cond = $c(0);

  always @(sig) begin
    if (cond) begin
      #1; $c("");
    end
  end
endmodule
