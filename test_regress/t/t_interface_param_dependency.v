// DESCRIPTION: Test interface parameter dependency resolution
//
// Test that interface/modport parameters can be accessed when the
// interface/modport is an IO port of the module.
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Paul Swirhun
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,
               expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

interface TEST_IF #(
    parameter int FOO = 1,
    parameter int BAR = FOO * 10
);
  logic [31:0] data;
  modport mp(input data);
endinterface

module submod_iface (
    output logic [31:0] result,
    TEST_IF iface
);
  assign result = iface.FOO + iface.BAR;
endmodule

module submod_modport (
    output logic [31:0] result,
    TEST_IF.mp mp
);
  assign result = mp.FOO + mp.BAR;
endmodule

// Test module that asserts interface parameter values - catches dependency bugs
module submod_assert #(
    parameter int EXPECTED_FOO = 0,
    parameter int EXPECTED_BAR = 0
) (
    TEST_IF iface
);
  initial begin
    // Verify the dependent parameter BAR is correctly computed in the module
    if (iface.FOO != EXPECTED_FOO) begin
      $error("FOO mismatch in module: expected %0d, got %0d", EXPECTED_FOO, iface.FOO);
    end
    if (iface.BAR != EXPECTED_BAR) begin
      $error("BAR dependency failed in module: expected %0d, got %0d", EXPECTED_BAR, iface.BAR);
    end
  end
endmodule

// Test parameterized interface chain: module parameter -> interface parameter -> submodule
module param_chain #(
    parameter int TOP_PARAM = 3
) (
    output logic [31:0] result
);
  // Interface gets parameter from module parameter
  TEST_IF #(.FOO(TOP_PARAM)) chain_iface ();

  // Submodule uses interface (FOO=3, BAR should be 30)
  submod_iface chain_sub (
      .result(result),
      .iface (chain_iface)
  );

  // Assert the chain works correctly
  submod_assert #(
      .EXPECTED_FOO(TOP_PARAM),
      .EXPECTED_BAR(TOP_PARAM * 10)
  ) chain_assert (
      .iface(chain_iface)
  );
endmodule


module t;
  // Test case 1: FOO specified, BAR should be FOO*10
  TEST_IF #(.FOO(5)) tif_1 ();

  // Test case 2: Both FOO and BAR specified explicitly
  TEST_IF #(
      .FOO(6),
      .BAR(66)
  ) tif_2 ();

  // Test case 3: Only BAR specified, FOO should be default
  TEST_IF #(.BAR(77)) tif_3 ();

  // Test case 4: Default parameters
  TEST_IF tif_4 ();

  logic [8:0][31:0] result;

  // Test interface as port parameter
  submod_iface u0 (
      .result(result[0]),
      .iface (tif_1)
  );
  submod_iface u1 (
      .result(result[1]),
      .iface (tif_2)
  );
  submod_iface u2 (
      .result(result[2]),
      .iface (tif_3)
  );
  submod_iface u3 (
      .result(result[3]),
      .iface (tif_4)
  );

  // Test modport as port parameter
  submod_modport u4 (
      .result(result[4]),
      .mp(tif_1)
  );
  submod_modport u5 (
      .result(result[5]),
      .mp(tif_2)
  );
  submod_modport u6 (
      .result(result[6]),
      .mp(tif_3)
  );
  submod_modport u7 (
      .result(result[7]),
      .mp(tif_4)
  );

  // Test that interface parameter dependencies are correctly resolved in modules
  submod_assert #(
      .EXPECTED_FOO(5),
      .EXPECTED_BAR(50)
  ) assert1 (
      .iface(tif_1)
  );

  // Test parameterized interface chain: module param -> interface param -> submodule
  param_chain #(.TOP_PARAM(4)) chain_test (.result(result[8]));

  // Allow hierarchichal references to locally declared interfaces only when HIERPARAM is waived
  /* verilator lint_off HIERPARAM */
  TEST_IF #(.FOO(3)) test_if_local ();
  logic [31:0] foo_local_1 = 32'(test_if_local.FOO);
  logic [31:0] bar_local_1 = 32'(test_if_local.BAR);
  localparam FOO_LOCAL = test_if_local.FOO;
  localparam BAR_LOCAL = test_if_local.BAR;
  logic [31:0] foo_local_2 = 32'(FOO_LOCAL);
  logic [31:0] bar_local_2 = 32'(BAR_LOCAL);
  /* verilator lint_on HIERPARAM */

  initial begin
    // Verify modules can access interface parameters correctly
    `checkd(result[0], 55);  // 5 + 50
    `checkd(result[1], 72);  // 6 + 66
    `checkd(result[2], 78);  // 1 + 77 (FOO default + BAR explicit)
    `checkd(result[3], 11);  // 1 + 10 (both defaults, BAR = FOO*10)

    // Verify modport access gives same results
    `checkd(result[4], 55);  // 5 + 50
    `checkd(result[5], 72);  // 6 + 66
    `checkd(result[6], 78);  // 1 + 77
    `checkd(result[7], 11);  // 1 + 10

    // Verify parameterized chain works
    `checkd(result[8], 44);  // 4 + 40 (TOP_PARAM=4, so FOO=4, BAR=40)

    `checkd(foo_local_1, 3);
    `checkd(bar_local_1, 30);
    `checkd(foo_local_2, 3);
    `checkd(bar_local_2, 30);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
