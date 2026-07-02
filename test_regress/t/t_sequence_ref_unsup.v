// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  sequence s_one;
    1;
  endsequence

  // s_one is referenced only from another sequence that is never expanded into
  // an assertion, so it is left referenced outside any assertion property.
  sequence s_two;
    s_one ##1 1;
  endsequence

endmodule
