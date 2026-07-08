// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t;
  int q[2][$];

  task automatic pop_q(input int qid, input int expected);
    int actual;
    actual = q[qid].pop_front();
    if (qid < 2 && actual !== expected) $stop;
  endtask

  initial begin
    for (int i = 0; i < 4; i++) begin
      q[i].push_back(i);
    end

    for (int i = 0; i < 4; i++) begin
      pop_q(i, i);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
