// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package P;
`ifndef TEST_NO_TYPEDEFS
  typedef enum enum_t;
  typedef struct struct_t;
  typedef union union_t;
  typedef class ClsB;
  typedef interface class IfC;
  typedef generic_t;
`endif

  class ClsA;
    enum_t m_e;  // <--- Error need forward decl (if TEST_NO_TYPEDEFS)
    struct_t m_s;  // <--- Error need forward decl (if TEST_NO_TYPEDEFS)
    union_t m_u;  // <--- Error need forward decl (if TEST_NO_TYPEDEFS)
    ClsB m_b;  // <--- Error need forward decl (if TEST_NO_TYPEDEFS)
    IfC m_i;  // <--- Error need forward decl (if TEST_NO_TYPEDEFS)
    generic_t m_g;  // <--- Error need forward decl (if TEST_NO_TYPEDEFS)
  endclass

  typedef enum {N = 0} enum_t;

  typedef struct packed {int s;} struct_t;
  typedef union packed {int s;} union_t;

  class ClsB;
  endclass

  interface class IfC;
  endclass

  typedef int generic_t;

endpackage

module t;
endmodule
