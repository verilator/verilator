// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// DESCRIPTION: Verilator: Invalid aggregate dtype comparisons
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Shou-Li Hsu.
// SPDX-License-Identifier: CC0-1.0

module t;
  typedef int    myint;
  typedef bit    mybit;
  typedef string mystr;
  typedef int    myval;
  typedef logic [31:0] mylogic;

  initial begin
    int queue_var[$] = '{1, 2, 3};
    int q1[$] = '{1, 2};
    bit q2[$] = '{1'b1, 1'b0};

    int d1[] = new[2];
    bit d2[] = new[2];

    int u1[2] = '{1, 2};
    int u2[2][1] = '{{1}, {2}};

    int a1[2] = '{1, 2};
    int a2[3] = '{1, 2, 3};

    int aa1[string];
    int aa2[int];

    int aa3[string];
    logic [3:0] aa4[string];

    myint bad1[2] = '{1, 2};
    mybit bad2[2] = '{1, 0};

    myval val1[mystr] = '{"foo": 123};
    mylogic val2[string] = '{"foo": 32'h12345678};

    myint aa5[string];
    myint aa6[int];
    aa5["a"] = 1;
    aa6[1] = 1;

    // queue vs scalar
    if (queue_var == 1) begin end

    // scalar vs queue
    if (1 == queue_var) begin end

    // queue with diff type
    if (q1 == q2) begin end

    // dyn array with diff type
    if (d1 == d2) begin end

    // unpacked diff dim
    if (u1 == u2) begin end

    // unpacked diff size
    if (a1 == a2) begin end

    // assoc array diff key type
    if (aa1 == aa2) begin end

    // assoc array diff value type
    if (aa3 == aa4) begin end

    // typedef mismatch in unpacked array
    if (bad1 == bad2) begin end

    // typedef mismatch in assoc array value
    if (val1 == val2) begin end

    // typedef mismatch in assoc array key
    if (aa5 == aa6) begin end
  end
endmodule
