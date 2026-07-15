// DESCRIPTION: Verilator: Transitive finish effect analysis
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

module t;
  task leaf;
    $finish;
  endtask

  task wrapper;
    leaf();
  endtask

  initial wrapper();
endmodule
