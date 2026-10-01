// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// DESCRIPTION: Verilator: Invalid aggregate dtype comparisons
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Shou-Li Hsu
// SPDX-License-Identifier: CC0-1.0

typedef struct {int val;} X_t;
typedef union {
  int val;
  int other;
} U_t;
typedef enum {
  A,
  B,
  C
} E_t;
module t;
  typedef int myint_t;
  typedef bit mybit_t;
  typedef string mystr_t;
  typedef int myval_t;
  typedef logic [31:0] mylogic_t;

  initial begin
    automatic int queue_var[$] = '{1, 2, 3};
    automatic int q1[$] = '{1, 2};
    automatic bit q2[$] = '{1'b1, 1'b0};

    automatic int d1[] = new[2];
    automatic bit d2[] = new[2];

    automatic int u1[2] = '{1, 2};
    automatic int u2[2][1] = '{{1}, {2}};

    automatic int a1[2] = '{1, 2};
    automatic int a2[3] = '{1, 2, 3};

    automatic int aa1[string];
    automatic int aa2[int];

    automatic int aa3[string];
    automatic logic [3:0] aa4[string];

    automatic myint_t bad1[2] = '{1, 2};
    automatic mybit_t bad2[2] = '{1, 0};

    automatic myval_t val1[mystr_t] = '{"foo": 123};
    automatic mylogic_t val2[string] = '{"foo": 32'h12345678};

    automatic myint_t aa5[string];
    automatic myint_t aa6[int];
    automatic X_t x = {2'h2};
    automatic E_t e;
    automatic U_t u = {2'h2};
    automatic struct {int val;} bad_s1;
    automatic struct {int val;} bad_s2;
    automatic
    union {
      int val;
      int other;
    }
    bad_u1;
    automatic
    union {
      int val;
      int other;
    }
    bad_u2;
    automatic
    enum {
      BAD_ENUM_A,
      BAD_ENUM_B
    }
    bad_e1;
    automatic
    enum {
      BAD_ENUM_C,
      BAD_ENUM_D
    }
    bad_e2;
    aa5["a"] = 1;
    aa6[1]   = 1;

    // unpacked struct vs scalar
    if (x == 2) begin
    end
    if (2 == x) begin
    end

    // unpacked union vs scalar
    if (u == 2) begin
    end
    if (2 == u) begin
    end

    // enum vs unpacked struct
    if (e == x) begin
    end
    if (x == e) begin
    end

    // Distinct anonymous unpacked structs
    if (bad_s1 == bad_s2) begin
    end

    // Distinct anonymous unpacked unions
    if (bad_u1 == bad_u2) begin
    end

    // Distinct anonymous enums
    if (bad_e1 == bad_e2) begin
    end

    // queue vs scalar
    if (queue_var == 1) begin
    end

    // scalar vs queue
    if (1 == queue_var) begin
    end

    // queue with diff type
    if (q1 == q2) begin
    end

    // dyn array with diff type
    if (d1 == d2) begin
    end

    // unpacked diff dim
    if (u1 == u2) begin
    end

    // unpacked diff size
    if (a1 == a2) begin
    end

    // assoc array diff key type
    if (aa1 == aa2) begin
    end

    // assoc array diff value type
    if (aa3 == aa4) begin
    end

    // typedef mismatch in unpacked array
    if (bad1 == bad2) begin
    end

    // typedef mismatch in assoc array value
    if (val1 == val2) begin
    end

    // typedef mismatch in assoc array key
    if (aa5 == aa6) begin
    end
  end
endmodule
