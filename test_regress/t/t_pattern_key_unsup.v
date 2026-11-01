// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;
  // Data type keys are legal in array patterns (IEEE 1800-2023 10.9.1), but only
  // supported in structure patterns
  int unpk[1] = '{int : 1};
  int assoc[int] = '{int : 2};
  int wild[*] = '{int : 3};
  int dt[] = '{int : 4};
  int qt[$] = '{int : 5};
  int dyn[];
  initial dyn = new[2] ('{int : 6});
endmodule
