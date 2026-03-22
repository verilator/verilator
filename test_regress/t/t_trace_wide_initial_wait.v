// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"

module t;
  logic [128:0] x = 0;

  always #10 x = ~x;

  initial begin
    #1;
    $dumpfile(`STRINGIFY(`TEST_DUMPFILE));
    $dumpvars();
    #5;
    x = 442093479423423857275364882039482723489;
    #5;
    #100;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
