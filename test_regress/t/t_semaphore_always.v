// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  semaphore s = new;

  initial begin
    s.put();
  end

  always @(posedge clk) begin
    s.get();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
