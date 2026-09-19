// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// An assignment pattern that carries its own data type, overriding a parameter whose
// declared type depends on an earlier parameter.  The pattern's type is used as-is, so
// no per-instance copy of the declared type is made.  Kept apart from t_param_pattern4
// as this must be the first such pin widthed to exercise that path.
typedef int arr_t[3];

module dut #(
    parameter int ARRAY_LEN = 3,
    parameter int ARRAY_PARAM[ARRAY_LEN] = '{2, 2, 4}
) (
    output int o_sum
);
  int sum;
  always_comb begin
    sum = 0;
    for (int i = 0; i < ARRAY_LEN; ++i) sum += ARRAY_PARAM[i];
  end
  assign o_sum = sum;
endmodule

module t;
  int o_typedpat;

  dut #(
      .ARRAY_LEN(3),
      .ARRAY_PARAM(arr_t'{1, 2, 3})
  ) u_typedpat (
      .o_sum(o_typedpat)
  );

  initial begin
    if (o_typedpat !== 6) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
