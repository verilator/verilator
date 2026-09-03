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

// The array's size parameter is not overridden, and its default references a
// further parameter that is, so substitution has to chain
module dut3 #(
    parameter int ARRAY_LEN = 2,
    parameter int ARRAY_LEN2 = ARRAY_LEN,
    parameter int ARRAY_PARAM[ARRAY_LEN2] = '{3, 5}
) (
    output int o_sum
);
  int sum;
  always_comb begin
    sum = 0;
    for (int i = 0; i < ARRAY_LEN2; ++i) sum += ARRAY_PARAM[i];
  end
  assign o_sum = sum;
endmodule

// Each default references the previous one twice, so substituting without folding
// each parameter's value would grow the data type exponentially.
module dut4 #(
    parameter int L0 = 1,
    parameter int L1 = (L0 + L0) / 2,
    parameter int L2 = (L1 + L1) / 2,
    parameter int L3 = (L2 + L2) / 2,
    parameter int L4 = (L3 + L3) / 2,
    parameter int L5 = (L4 + L4) / 2,
    parameter int L6 = (L5 + L5) / 2,
    parameter int L7 = (L6 + L6) / 2,
    parameter int L8 = (L7 + L7) / 2,
    parameter int L9 = (L8 + L8) / 2,
    parameter int L10 = (L9 + L9) / 2,
    parameter int L11 = (L10 + L10) / 2,
    parameter int L12 = (L11 + L11) / 2,
    parameter int L13 = (L12 + L12) / 2,
    parameter int L14 = (L13 + L13) / 2,
    parameter int L15 = (L14 + L14) / 2,
    parameter int L16 = (L15 + L15) / 2,
    parameter int L17 = (L16 + L16) / 2,
    parameter int L18 = (L17 + L17) / 2,
    parameter int L19 = (L18 + L18) / 2,
    parameter int L20 = (L19 + L19) / 2,
    parameter int ARRAY_PARAM[L20] = '{default: 1}
) (
    output int o_sum
);
  int sum;
  always_comb begin
    sum = 0;
    for (int i = 0; i < L20; ++i) sum += ARRAY_PARAM[i];
  end
  assign o_sum = sum;
endmodule

// The array's element type is a type parameter, so substitution must retarget the
// type reference too, else it is left pointing into the template module
module dut5 #(
    parameter type T = byte,
    parameter int ARRAY_LEN = 2,
    parameter T ARRAY_PARAM[ARRAY_LEN] = '{3, 5}
) (
    output int o_sum
);
  int sum;
  always_comb begin
    sum = 0;
    for (int i = 0; i < ARRAY_LEN; ++i) sum += int'(ARRAY_PARAM[i]);
  end
  assign o_sum = sum;
endmodule

// Same, for an interface
interface Ifc #(
    parameter int ARRAY_LEN = 3,
    parameter int ARRAY_PARAM[ARRAY_LEN] = '{2, 2, 4}
);
  function automatic int getSum();
    getSum = 0;
    for (int i = 0; i < ARRAY_LEN; ++i) getSum += ARRAY_PARAM[i];
  endfunction
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
  int o_chain;
  int o_chaindef;
  int o_exp;
  int o_type;
  int o_typedef;
  int o_typelen;

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

  // ARRAY_LEN2 keeps its default, which resolves through the overridden ARRAY_LEN
  dut3 #(
      .ARRAY_LEN(4),
      .ARRAY_PARAM('{1, 2, 3, 4})
  ) u_chain (
      .o_sum(o_chain)
  );

  dut3 u_chaindef (.o_sum(o_chaindef));

  dut4 #(
      .L0(4),
      .ARRAY_PARAM('{1, 2, 3, 4})
  ) u_exp (
      .o_sum(o_exp)
  );

  // Type parameter overridden, along with the size
  dut5 #(
      .T(int),
      .ARRAY_LEN(3),
      .ARRAY_PARAM('{1, 2, 3})
  ) u_type (
      .o_sum(o_type)
  );

  // Type parameter keeps its default while the size is overridden
  dut5 #(
      .ARRAY_LEN(4),
      .ARRAY_PARAM('{1, 2, 3, 4})
  ) u_typedef (
      .o_sum(o_typedef)
  );

  // Type parameter overridden while the size keeps its default
  dut5 #(
      .T(int),
      .ARRAY_PARAM('{5, 6})
  ) u_typelen (
      .o_sum(o_typelen)
  );

  // Virtual interface handle to a parameterized interface, a distinct path from
  // the interface instantiation above
  virtual Ifc #(
      .ARRAY_LEN(4),
      .ARRAY_PARAM('{2, 2, 2, 4})
  ) v_wide;

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
    if (o_chain !== 10) $stop;
    if (o_chaindef !== 8) $stop;
    if (o_exp !== 10) $stop;
    if (o_type !== 6) $stop;
    if (o_typedef !== 10) $stop;
    if (o_typelen !== 11) $stop;
    if (i_default.getSum() !== 8) $stop;
    if (i_wide.getSum() !== 10) $stop;
    v_wide = i_wide;
    if (v_wide.getSum() !== 10) $stop;
    if (Cls#()::sum() !== 8) $stop;
    if (Cls#(4, '{2, 2, 2, 4})::sum() !== 10) $stop;
    if (Cls#(.ARRAY_PARAM('{5, 6, 7}))::sum() !== 18) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
