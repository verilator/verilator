// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define TRY_ASSIGN(a,b) a = b
`define TRY_CAST(a,b) a = type(a)'(b)
`ifdef VERILATOR
`define TRY_DYNAMIC(a,b)  // UNSUP $cast
`define TRY_BAD(a,b)  // UNSUP $cast
`else
`define TRY_DYNAMIC(a,b) if (1 != $cast(a, b)) $stop
`define TRY_BAD(a,b) if (0 != $cast(a, b)) $stop
`endif

`define MATCHING(a,b) `TRY_ASSIGN(a,b)
`define EQUIVALENT(a,b) `TRY_ASSIGN(a,b)
`define COMPATIBLE(a,b) `TRY_ASSIGN(a,b)
`define CAST_COMPATIBLE(a,b) `TRY_CAST(a,b)
`define CAST_COMPATIBLE_ENUM(a,b) `TRY_CAST(a,b)
`define CAST_COMPATIBLE_DYNAMIC(a,b) `TRY_DYNAMIC(a,b)
`define INCOMPATIBLE(a,b) `TRY_BAD(a,b)

`define STRING_LITERAL  "literal"   // IEEE 5.9 - to packed or unpacked per IEEE 6.24

class Base;
endclass
class BaseExtended extends Base;
endclass
class Other;
endclass

typedef enum { A_ZERO, A_ONE } Enum_A_t;
typedef enum { B_ZERO, B_ONE } Enum_B_t;

typedef int int_t;

typedef struct packed { int a; int b; } stpack_t;

typedef bit signed [7:0] simple_a_t;
typedef bit signed [7:0] simple_a1_t;

module t (/*AUTOARG*/);

   real    v_real;      // IEEE 6.12.2 - by rounding
   string  v_string;
   int     v_int;
   int_t   v_int_t;
   chandle v_chandle;
   Enum_A_t  v_enum_a;
   Enum_A_t  v_enum_a1;
   Enum_B_t  v_enum_b;
   stpack_t  v_stpack_a;
   stpack_t  v_stpack_a1;
   simple_a_t  v_simple_a;
   simple_a1_t  v_simple_a1;
   int     v_unpk_a[2][3];
   int     v_unpk_a1[2][3];
   int     v_assoc_a[string];
   int     v_assoc_a1[string];
   int     v_assoc_b[int];
   int     v_assoc_c[bit[31:0]];

   int     v_q_a[$];
   int     v_q_a1[$];
   real    v_q_b[$];

   bit [3:0][7:0] v_2thirtytwo_a;
   bit [3:0][7:0] v_2thirtytwo_b;
   logic [3:0][7:0] v_4thirtytwo_a;
   logic [3:0][7:0] v_4thirtytwo_b;

   Base v_cls_a;
   Base v_cls_a1;
   BaseExtended v_cls_ab;
   Other v_cls_b;

   // verilator lint_off REALCVT

   initial begin
      // 6.22.1
      `MATCHING(v_real, v_real);
      `MATCHING(v_string, v_string);
      `MATCHING(v_int, v_int);
      `MATCHING(v_chandle, v_chandle);
      `MATCHING(v_int, v_int_t);
      `MATCHING(v_stpack_a, v_stpack_a1);
      `MATCHING(v_simple_a, v_simple_a1);
      `MATCHING(v_unpk_a, v_unpk_a1);
      `MATCHING(v_assoc_a, v_assoc_a1);
      `MATCHING(v_q_a, v_q_a1);
      `MATCHING(v_int, v_2thirtytwo_a);
      `MATCHING(v_cls_a, v_cls_a1);
      `MATCHING(v_cls_a, v_cls_ab);
      // 6.22.2
      `EQUIVALENT(v_int, v_2thirtytwo_a);
`ifndef NC
`ifndef VCS
      `EQUIVALENT(v_assoc_b, v_assoc_c);  // Spec says equivalent, but simulators disagree
`endif
`endif
      // 6.22.3
      `COMPATIBLE(v_string, `STRING_LITERAL);
      `COMPATIBLE(v_int, v_enum_a);
      `COMPATIBLE(v_int, v_real);
      `COMPATIBLE(v_real, v_int);
      // 6.22.4->5.9
`ifndef NC
      `CAST_COMPATIBLE(v_string, v_int);
`endif
      // 6.22.4->6.19.3
`ifndef NC
      `CAST_COMPATIBLE_ENUM(v_enum_a, v_int);
      `CAST_COMPATIBLE_ENUM(v_enum_a, v_enum_b);
`endif
      `CAST_COMPATIBLE_DYNAMIC(v_cls_ab, v_cls_a);
      // 6.22.5 incompatible
      `INCOMPATIBLE(v_cls_ab, v_int);
`ifndef VCS
      `INCOMPATIBLE(v_real, v_assoc_a);
      `INCOMPATIBLE(v_real, v_q_a);
`endif
`ifndef VCS
 `ifndef VERILATOR
      `INCOMPATIBLE(v_chandle, v_int);
 `endif
`endif
`ifndef NC
      `INCOMPATIBLE(v_cls_a, v_cls_b);
`endif

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
