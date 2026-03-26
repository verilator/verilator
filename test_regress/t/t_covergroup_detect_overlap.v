// DESCRIPTION: Verilator: covergroup detect_overlap diagnostics
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 OpenAI
// SPDX-License-Identifier: CC0-1.0

module t;

  int a;

  covergroup cg;
    option.detect_overlap = 1;

    cp_on: coverpoint a {
      bins low = {[0:2]};
      bins mid = {[2:4]};
    }

    cp_off: coverpoint a {
      option.detect_overlap = 0;
      bins low = {[8:10]};
      bins mid = {[10:12]};
    }
  endgroup

endmodule
