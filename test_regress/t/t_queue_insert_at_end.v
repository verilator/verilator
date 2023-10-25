// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t();
  initial begin
    int queue[$];

    queue.insert(0, 0);
    if (queue.size() != 1) $stop;

    queue.insert(1, 1);
    if (queue.size() != 2) $stop;

    if (queue[0] != 0) $stop;
    if (queue[1] != 1) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
