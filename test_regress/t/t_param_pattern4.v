// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Unpacked array parameter whose size depends on an earlier parameter that is
// also overridden by the same instantiation.
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

// Two parameters sized by the same earlier parameter, so one instantiation
// substitutes into two separate patterns
module dut2 #(
    parameter int ARRAY_LEN = 3,
    parameter int ARRAY_A[ARRAY_LEN] = '{1, 1, 1},
    parameter int ARRAY_B[ARRAY_LEN] = '{1, 1, 1}
) (
    output int o_sum
);
  int sum;
  always_comb begin
    sum = 0;
    for (int i = 0; i < ARRAY_LEN; ++i) sum += ARRAY_A[i] + ARRAY_B[i];
  end
  assign o_sum = sum;
endmodule

// Same, for an interface
interface Ifc #(
    parameter int ARRAY_LEN = 3,
    parameter int ARRAY_PARAM[ARRAY_LEN] = '{2, 2, 4}
);
  int sum;
  always_comb begin
    sum = 0;
    for (int i = 0; i < ARRAY_LEN; ++i) sum += ARRAY_PARAM[i];
  end
endinterface

// Same, for a class
class Cls #(
    parameter int ARRAY_LEN = 3,
    parameter int ARRAY_PARAM[ARRAY_LEN] = '{2, 2, 4}
);
  static function int sum();
    sum = 0;
    for (int i = 0; i < ARRAY_LEN; ++i) sum += ARRAY_PARAM[i];
  endfunction
endclass

module t;
  int o_default;
  int o_wide;
  int o_narrow;
  int o_deflen;
  int o_two;
  int o_emptylen;

  dut u_default (.o_sum(o_default));

  dut #(
      .ARRAY_LEN(4),
      .ARRAY_PARAM('{2, 2, 2, 4})
  ) u_wide (
      .o_sum(o_wide)
  );

  dut #(
      .ARRAY_LEN(2),
      .ARRAY_PARAM('{2, 4})
  ) u_narrow (
      .o_sum(o_narrow)
  );

  // Overrides the array but not its size, so the size uses the default
  dut #(
      .ARRAY_PARAM('{5, 6, 7})
  ) u_deflen (
      .o_sum(o_deflen)
  );

  // Both patterns resolve against the same overriding pins
  dut2 #(
      .ARRAY_LEN(2),
      .ARRAY_A('{1, 2}),
      .ARRAY_B('{3, 4})
  ) u_two (
      .o_sum(o_two)
  );

  // Empty override, so the size still comes from the default
  dut #(
      .ARRAY_LEN(),
      .ARRAY_PARAM('{5, 6, 7})
  ) u_emptylen (
      .o_sum(o_emptylen)
  );

  Ifc i_default ();
  Ifc #(
      .ARRAY_LEN(4),
      .ARRAY_PARAM('{2, 2, 2, 4})
  ) i_wide ();

  initial begin
    if (o_default !== 8) $stop;
    if (o_wide !== 10) $stop;
    if (o_narrow !== 6) $stop;
    if (o_deflen !== 18) $stop;
    if (o_two !== 10) $stop;
    if (o_emptylen !== 18) $stop;
    if (i_default.sum !== 8) $stop;
    if (i_wide.sum !== 10) $stop;
    if (Cls#()::sum() !== 8) $stop;
    if (Cls#(4, '{2, 2, 2, 4})::sum() !== 10) $stop;
    if (Cls#(.ARRAY_PARAM('{5, 6, 7}))::sum() !== 18) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
