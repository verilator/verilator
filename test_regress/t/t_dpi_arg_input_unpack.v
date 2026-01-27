// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2020 Yutetsu TAKATSUKASA
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VCS
 `define NO_TIME
`endif

`ifdef NC
 `define NO_TIME
 `define NO_INTEGER
 `define NO_SHORTREAL
`endif

`ifdef MS
 `define NO_BITS_TO_SCALAR
`endif

`ifdef VERILATOR
 `define NO_SHORTREAL
 `define NO_UNPACK_STRUCT
`else
`endif

`ifdef NO_BITS_TO_SCALAR
 `define ARE_SAME(act, exp) ((act) == (exp))
`else
 `define ARE_SAME(act, exp) ((act) == (($bits(act))'(exp)))
`endif

`define CHECK_VAL(act, exp) if (`ARE_SAME(act, exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":", (act), " as expected"); \
     end else begin \
        $display("Mismatch %s expected:%d actual:%d at %d", `"act`", \
                 int'(exp), int'(act), `__LINE__); \
          $stop; \
            end

`define CHECK_0D(val) \
  `CHECK_VAL((val), 42)
`define CHECK_1D(val) \
  `CHECK_VAL(val[0], 43); \
  `CHECK_VAL(val[1], 44)
`define CHECK_2D(val) \
  `CHECK_VAL(val[0][1], 45); \
  `CHECK_VAL(val[1][1], 46); \
  `CHECK_VAL(val[2][1], 47)
`define CHECK_3D(val) \
  `CHECK_VAL(val[0][0][0], 48); \
  `CHECK_VAL(val[1][0][0], 49); \
  `CHECK_VAL(val[2][0][0], 50); \
  `CHECK_VAL(val[3][0][0], 51)

`define CHECK_1D1(val) \
  `CHECK_VAL(val[0], 52)
`define CHECK_2D1(val) \
  `CHECK_VAL(val[0][0], 53)
`define CHECK_3D1(val) \
  `CHECK_VAL(val[0][0][0], 54)

`define SET_VALUES(val) \
/* verilator lint_off WIDTH */ \
val[3][2][1] = 42; \
val[2][1][0] = 43; val[2][1][1] = 44; \
val[1][0][1] = 45; val[1][1][1] = 46; val[1][2][1] = 47; \
val[0][0][0] = 48; val[1][0][0] = 49; val[2][0][0] = 50; val[3][0][0] = 51 \
/* verilator lint_on WIDTH */

module t;

   localparam ENABLE_VERBOSE_MESSAGE = 0;

   // Legal input argument types for DPI functions

   //======================================================================
   // Type definitions
   //======================================================================

   typedef byte              byte_array_t[4][3][2];
   typedef byte              byte_array1_t[1][1][1];
   typedef byte unsigned     byte_unsigned_array_t[4][3][2];
   typedef byte unsigned     byte_unsigned_array1_t[1][1][1];
   typedef shortint          shortint_array_t[4][3][2];
   typedef shortint          shortint_array1_t[1][1][1];
   typedef shortint unsigned shortint_unsigned_array_t[4][3][2];
   typedef shortint unsigned shortint_unsigned_array1_t[1][1][1];
   typedef int               int_array_t[4][3][2];
   typedef int               int_array1_t[1][1][1];
   typedef int unsigned      int_unsigned_array_t[4][3][2];
   typedef int unsigned      int_unsigned_array1_t[1][1][1];
   typedef longint           longint_array_t[4][3][2];
   typedef longint           longint_array1_t[1][1][1];
   typedef longint unsigned  longint_unsigned_array_t[4][3][2];
   typedef longint unsigned  longint_unsigned_array1_t[1][1][1];
`ifndef NO_TIME
   typedef time              time_array_t[4][3][2];
   typedef time              time_array1_t[1][1][1];
`endif
`ifndef NO_INTEGER
   typedef integer           integer_array_t[4][3][2];
   typedef integer           integer_array1_t[1][1][1];
`endif
   typedef real              real_array_t[4][3][2];
   typedef real              real_array1_t[1][1][1];
`ifndef NO_SHORTREAL
   typedef shortreal         shortreal_array_t[4][3][2];
   typedef shortreal         shortreal_array1_t[1][1][1];
`endif
   typedef chandle           chandle_array_t[4][3][2];
   typedef chandle           chandle_array1_t[1][1][1];
   typedef string            string_array_t[4][3][2];
   typedef string            string_array1_t[1][1][1];
   typedef bit               bit1_array_t[4][3][2];
   typedef bit               bit1_array1_t[1][1][1];
   typedef bit [6:0]         bit7_array_t[4][3][2];
   typedef bit [6:0]         bit7_array1_t[1][1][1];
   typedef bit [120:0]       bit121_array_t[4][3][2];
   typedef bit [120:0]       bit121_array1_t[1][1][1];
   typedef logic             logic1_array_t[4][3][2];
   typedef logic             logic1_array1_t[1][1][1];
   typedef logic [6:0]       logic7_array_t[4][3][2];
   typedef logic [6:0]       logic7_array1_t[1][1][1];
   typedef logic [120:0]     logic121_array_t[4][3][2];
   typedef logic [120:0]     logic121_array1_t[1][1][1];

   typedef struct            packed {
      logic [6:0]            val;
   } pack_struct_t;
   typedef pack_struct_t pack_struct_array_t[4][3][2];
   typedef pack_struct_t pack_struct_array1_t[1][1][1];
`ifndef NO_UNPACK_STRUCT
   typedef struct            {
      logic [120:0]          val;
   } unpack_struct_t;
   typedef unpack_struct_t unpack_struct_array_t[4][3][2];
   typedef unpack_struct_t unpack_struct_array1_t[1][1][1];
`endif

   //======================================================================
   // Imports
   //======================================================================

   // Returns non-null pointer
   import "DPI-C" function chandle get_non_null();

   import "DPI-C" function void i_byte_0d(input byte val);
   import "DPI-C" function void i_byte_1d(input byte val[2]);
   import "DPI-C" function void i_byte_2d(input byte val[3][2]);
   import "DPI-C" function void i_byte_3d(input byte_array_t val);
   import "DPI-C" function void i_byte_1d1(input byte val[1]);
   import "DPI-C" function void i_byte_2d1(input byte val[1][1]);
   import "DPI-C" function void i_byte_3d1(input byte_array1_t val);

   import "DPI-C" function void i_byte_unsigned_0d(input byte unsigned val);
   import "DPI-C" function void i_byte_unsigned_1d(input byte unsigned val[2]);
   import "DPI-C" function void i_byte_unsigned_2d(input byte unsigned val[3][2]);
   import "DPI-C" function void i_byte_unsigned_3d(input byte_unsigned_array_t val);
   import "DPI-C" function void i_byte_unsigned_1d1(input byte unsigned val[1]);
   import "DPI-C" function void i_byte_unsigned_2d1(input byte unsigned val[1][1]);
   import "DPI-C" function void i_byte_unsigned_3d1(input byte_unsigned_array1_t val);

   import "DPI-C" function void i_shortint_0d(input shortint val);
   import "DPI-C" function void i_shortint_1d(input shortint val[2]);
   import "DPI-C" function void i_shortint_2d(input shortint val[3][2]);
   import "DPI-C" function void i_shortint_3d(input shortint_array_t val);
   import "DPI-C" function void i_shortint_1d1(input shortint val[1]);
   import "DPI-C" function void i_shortint_2d1(input shortint val[1][1]);
   import "DPI-C" function void i_shortint_3d1(input shortint_array1_t val);

   import "DPI-C" function void i_shortint_unsigned_0d(input shortint unsigned val);
   import "DPI-C" function void i_shortint_unsigned_1d(input shortint unsigned val[2]);
   import "DPI-C" function void i_shortint_unsigned_2d(input shortint unsigned val[3][2]);
   import "DPI-C" function void i_shortint_unsigned_3d(input shortint_unsigned_array_t val);
   import "DPI-C" function void i_shortint_unsigned_1d1(input shortint unsigned val[1]);
   import "DPI-C" function void i_shortint_unsigned_2d1(input shortint unsigned val[1][1]);
   import "DPI-C" function void i_shortint_unsigned_3d1(input shortint_unsigned_array1_t val);

   import "DPI-C" function void i_int_0d(input int val);
   import "DPI-C" function void i_int_1d(input int val[2]);
   import "DPI-C" function void i_int_2d(input int val[3][2]);
   import "DPI-C" function void i_int_3d(input int_array_t val);
   import "DPI-C" function void i_int_1d1(input int val[1]);
   import "DPI-C" function void i_int_2d1(input int val[1][1]);
   import "DPI-C" function void i_int_3d1(input int_array1_t val);

   import "DPI-C" function void i_int_unsigned_0d(input int unsigned val);
   import "DPI-C" function void i_int_unsigned_1d(input int unsigned val[2]);
   import "DPI-C" function void i_int_unsigned_2d(input int unsigned val[3][2]);
   import "DPI-C" function void i_int_unsigned_3d(input int_unsigned_array_t val);
   import "DPI-C" function void i_int_unsigned_1d1(input int unsigned val[1]);
   import "DPI-C" function void i_int_unsigned_2d1(input int unsigned val[1][1]);
   import "DPI-C" function void i_int_unsigned_3d1(input int_unsigned_array1_t val);

   import "DPI-C" function void i_longint_0d(input longint val);
   import "DPI-C" function void i_longint_1d(input longint val[2]);
   import "DPI-C" function void i_longint_2d(input longint val[3][2]);
   import "DPI-C" function void i_longint_3d(input longint_array_t val);
   import "DPI-C" function void i_longint_1d1(input longint val[1]);
   import "DPI-C" function void i_longint_2d1(input longint val[1][1]);
   import "DPI-C" function void i_longint_3d1(input longint_array1_t val);

   import "DPI-C" function void i_longint_unsigned_0d(input longint unsigned val);
   import "DPI-C" function void i_longint_unsigned_1d(input longint unsigned val[2]);
   import "DPI-C" function void i_longint_unsigned_2d(input longint unsigned val[3][2]);
   import "DPI-C" function void i_longint_unsigned_3d(input longint_unsigned_array_t val);
   import "DPI-C" function void i_longint_unsigned_1d1(input longint unsigned val[1]);
   import "DPI-C" function void i_longint_unsigned_2d1(input longint unsigned val[1][1]);
   import "DPI-C" function void i_longint_unsigned_3d1(input longint_unsigned_array1_t val);

`ifndef NO_TIME
   import "DPI-C" function void i_time_0d(input time val);
   import "DPI-C" function void i_time_1d(input time val[2]);
   import "DPI-C" function void i_time_2d(input time val[3][2]);
   import "DPI-C" function void i_time_3d(input time_array_t val);
   import "DPI-C" function void i_time_1d1(input time val[1]);
   import "DPI-C" function void i_time_2d1(input time val[1][1]);
   import "DPI-C" function void i_time_3d1(input time_array1_t val);
`endif

`ifndef NO_INTEGER
   import "DPI-C" function void i_integer_0d(input integer val);
   import "DPI-C" function void i_integer_1d(input integer val[2]);
   import "DPI-C" function void i_integer_2d(input integer val[3][2]);
   import "DPI-C" function void i_integer_3d(input integer_array_t val);
   import "DPI-C" function void i_integer_1d1(input integer val[1]);
   import "DPI-C" function void i_integer_2d1(input integer val[1][1]);
   import "DPI-C" function void i_integer_3d1(input integer_array1_t val);
`endif

   import "DPI-C" function void i_real_0d(input real val);
   import "DPI-C" function void i_real_1d(input real val[2]);
   import "DPI-C" function void i_real_2d(input real val[3][2]);
   import "DPI-C" function void i_real_3d(input real_array_t val);
   import "DPI-C" function void i_real_1d1(input real val[1]);
   import "DPI-C" function void i_real_2d1(input real val[1][1]);
   import "DPI-C" function void i_real_3d1(input real_array1_t val);

`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal_0d(input shortreal val);
   import "DPI-C" function void i_shortreal_1d(input shortreal val[2]);
   import "DPI-C" function void i_shortreal_2d(input shortreal val[3][2]);
   import "DPI-C" function void i_shortreal_3d(input shortreal_array_t val);
   import "DPI-C" function void i_shortreal_1d1(input shortreal val[1]);
   import "DPI-C" function void i_shortreal_2d1(input shortreal val[1][1]);
   import "DPI-C" function void i_shortreal_3d1(input shortreal_array1_t val);
`endif

   import "DPI-C" function void i_chandle_0d(input chandle val);
   import "DPI-C" function void i_chandle_1d(input chandle val[2]);
   import "DPI-C" function void i_chandle_2d(input chandle val[3][2]);
   import "DPI-C" function void i_chandle_3d(input chandle_array_t val);
   import "DPI-C" function void i_chandle_1d1(input chandle val[1]);
   import "DPI-C" function void i_chandle_2d1(input chandle val[1][1]);
   import "DPI-C" function void i_chandle_3d1(input chandle_array1_t val);

   import "DPI-C" function void i_string_0d(input string val);
   import "DPI-C" function void i_string_1d(input string val[2]);
   import "DPI-C" function void i_string_2d(input string val[3][2]);
   import "DPI-C" function void i_string_3d(input string_array_t val);
   import "DPI-C" function void i_string_1d1(input string val[1]);
   import "DPI-C" function void i_string_2d1(input string val[1][1]);
   import "DPI-C" function void i_string_3d1(input string_array1_t val);

   import "DPI-C" function void i_bit1_0d(input bit val);
   import "DPI-C" function void i_bit1_1d(input bit val[2]);
   import "DPI-C" function void i_bit1_2d(input bit val[3][2]);
   import "DPI-C" function void i_bit1_3d(input bit1_array_t val);
   import "DPI-C" function void i_bit1_1d1(input bit val[1]);
   import "DPI-C" function void i_bit1_2d1(input bit val[1][1]);
   import "DPI-C" function void i_bit1_3d1(input bit1_array1_t val);

   import "DPI-C" function void i_bit7_0d(input bit[6:0] val);
   import "DPI-C" function void i_bit7_1d(input bit[6:0] val[2]);
   import "DPI-C" function void i_bit7_2d(input bit[6:0] val[3][2]);
   import "DPI-C" function void i_bit7_3d(input bit7_array_t val);
   import "DPI-C" function void i_bit7_1d1(input bit[6:0] val[1]);
   import "DPI-C" function void i_bit7_2d1(input bit[6:0] val[1][1]);
   import "DPI-C" function void i_bit7_3d1(input bit7_array1_t val);

   import "DPI-C" function void i_bit121_0d(input bit[120:0] val);
   import "DPI-C" function void i_bit121_1d(input bit[120:0] val[2]);
   import "DPI-C" function void i_bit121_2d(input bit[120:0] val[3][2]);
   import "DPI-C" function void i_bit121_3d(input bit121_array_t val);
   import "DPI-C" function void i_bit121_1d1(input bit[120:0] val[1]);
   import "DPI-C" function void i_bit121_2d1(input bit[120:0] val[1][1]);
   import "DPI-C" function void i_bit121_3d1(input bit121_array1_t val);

   import "DPI-C" function void i_logic1_0d(input logic val);
   import "DPI-C" function void i_logic1_1d(input logic val[2]);
   import "DPI-C" function void i_logic1_2d(input logic val[3][2]);
   import "DPI-C" function void i_logic1_3d(input logic1_array_t val);
   import "DPI-C" function void i_logic1_1d1(input logic val[1]);
   import "DPI-C" function void i_logic1_2d1(input logic val[1][1]);
   import "DPI-C" function void i_logic1_3d1(input logic1_array1_t val);

   import "DPI-C" function void i_logic7_0d(input logic[6:0] val);
   import "DPI-C" function void i_logic7_1d(input logic[6:0] val[2]);
   import "DPI-C" function void i_logic7_2d(input logic[6:0] val[3][2]);
   import "DPI-C" function void i_logic7_3d(input logic7_array_t val);
   import "DPI-C" function void i_logic7_1d1(input logic[6:0] val[1]);
   import "DPI-C" function void i_logic7_2d1(input logic[6:0] val[1][1]);
   import "DPI-C" function void i_logic7_3d1(input logic7_array1_t val);

   import "DPI-C" function void i_logic121_0d(input logic[120:0] val);
   import "DPI-C" function void i_logic121_1d(input logic[120:0] val[2]);
   import "DPI-C" function void i_logic121_2d(input logic[120:0] val[3][2]);
   import "DPI-C" function void i_logic121_3d(input logic121_array_t val);
   import "DPI-C" function void i_logic121_1d1(input logic[120:0] val[1]);
   import "DPI-C" function void i_logic121_2d1(input logic[120:0] val[1][1]);
   import "DPI-C" function void i_logic121_3d1(input logic121_array1_t val);

   import "DPI-C" function void i_pack_struct_0d(input pack_struct_t val);
   import "DPI-C" function void i_pack_struct_1d(input pack_struct_t val[2]);
   import "DPI-C" function void i_pack_struct_2d(input pack_struct_t val[3][2]);
   import "DPI-C" function void i_pack_struct_3d(input pack_struct_array_t val);
   import "DPI-C" function void i_pack_struct_1d1(input pack_struct_t val[1]);
   import "DPI-C" function void i_pack_struct_2d1(input pack_struct_t val[1][1]);
   import "DPI-C" function void i_pack_struct_3d1(input pack_struct_array1_t val);

`ifndef NO_UNPACK_STRUCT
   import "DPI-C" function void i_unpack_struct_0d(input unpack_struct_t val);
   import "DPI-C" function void i_unpack_struct_1d(input unpack_struct_t val[2]);
   import "DPI-C" function void i_unpack_struct_2d(input unpack_struct_t val[3][2]);
   import "DPI-C" function void i_unpack_struct_3d(input unpack_struct_array_t val);
   import "DPI-C" function void i_unpack_struct_1d1(input unpack_struct_t val[1]);
   import "DPI-C" function void i_unpack_struct_2d1(input unpack_struct_t val[1][1]);
   import "DPI-C" function void i_unpack_struct_3d1(input unpack_struct_array1_t val);
`endif


   //======================================================================
   // Exports
   //======================================================================

   export "DPI-C" function e_byte_0d;
   export "DPI-C" function e_byte_1d;
   export "DPI-C" function e_byte_2d;
   export "DPI-C" function e_byte_3d;
   export "DPI-C" function e_byte_1d1;
   export "DPI-C" function e_byte_2d1;
   export "DPI-C" function e_byte_3d1;

   export "DPI-C" function e_byte_unsigned_0d;
   export "DPI-C" function e_byte_unsigned_1d;
   export "DPI-C" function e_byte_unsigned_2d;
   export "DPI-C" function e_byte_unsigned_3d;
   export "DPI-C" function e_byte_unsigned_1d1;
   export "DPI-C" function e_byte_unsigned_2d1;
   export "DPI-C" function e_byte_unsigned_3d1;

   export "DPI-C" function e_shortint_0d;
   export "DPI-C" function e_shortint_1d;
   export "DPI-C" function e_shortint_2d;
   export "DPI-C" function e_shortint_3d;
   export "DPI-C" function e_shortint_1d1;
   export "DPI-C" function e_shortint_2d1;
   export "DPI-C" function e_shortint_3d1;

   export "DPI-C" function e_shortint_unsigned_0d;
   export "DPI-C" function e_shortint_unsigned_1d;
   export "DPI-C" function e_shortint_unsigned_2d;
   export "DPI-C" function e_shortint_unsigned_3d;
   export "DPI-C" function e_shortint_unsigned_1d1;
   export "DPI-C" function e_shortint_unsigned_2d1;
   export "DPI-C" function e_shortint_unsigned_3d1;

   export "DPI-C" function e_int_0d;
   export "DPI-C" function e_int_1d;
   export "DPI-C" function e_int_2d;
   export "DPI-C" function e_int_3d;
   export "DPI-C" function e_int_1d1;
   export "DPI-C" function e_int_2d1;
   export "DPI-C" function e_int_3d1;

   export "DPI-C" function e_int_unsigned_0d;
   export "DPI-C" function e_int_unsigned_1d;
   export "DPI-C" function e_int_unsigned_2d;
   export "DPI-C" function e_int_unsigned_3d;
   export "DPI-C" function e_int_unsigned_1d1;
   export "DPI-C" function e_int_unsigned_2d1;
   export "DPI-C" function e_int_unsigned_3d1;

   export "DPI-C" function e_longint_0d;
   export "DPI-C" function e_longint_1d;
   export "DPI-C" function e_longint_2d;
   export "DPI-C" function e_longint_3d;
   export "DPI-C" function e_longint_1d1;
   export "DPI-C" function e_longint_2d1;
   export "DPI-C" function e_longint_3d1;

   export "DPI-C" function e_longint_unsigned_0d;
   export "DPI-C" function e_longint_unsigned_1d;
   export "DPI-C" function e_longint_unsigned_2d;
   export "DPI-C" function e_longint_unsigned_3d;
   export "DPI-C" function e_longint_unsigned_1d1;
   export "DPI-C" function e_longint_unsigned_2d1;
   export "DPI-C" function e_longint_unsigned_3d1;

`ifndef NO_TIME
   export "DPI-C" function e_time_0d;
   export "DPI-C" function e_time_1d;
   export "DPI-C" function e_time_2d;
   export "DPI-C" function e_time_3d;
   export "DPI-C" function e_time_1d1;
   export "DPI-C" function e_time_2d1;
   export "DPI-C" function e_time_3d1;
`endif

`ifndef NO_INTEGER
   export "DPI-C" function e_integer_0d;
   export "DPI-C" function e_integer_1d;
   export "DPI-C" function e_integer_2d;
   export "DPI-C" function e_integer_3d;
   export "DPI-C" function e_integer_1d1;
   export "DPI-C" function e_integer_2d1;
   export "DPI-C" function e_integer_3d1;
`endif

   export "DPI-C" function e_real_0d;
   export "DPI-C" function e_real_1d;
   export "DPI-C" function e_real_2d;
   export "DPI-C" function e_real_3d;
   export "DPI-C" function e_real_1d1;
   export "DPI-C" function e_real_2d1;
   export "DPI-C" function e_real_3d1;

`ifndef NO_SHORTREAL
   export "DPI-C" function e_shortreal_0d;
   export "DPI-C" function e_shortreal_1d;
   export "DPI-C" function e_shortreal_2d;
   export "DPI-C" function e_shortreal_3d;
   export "DPI-C" function e_shortreal_1d1;
   export "DPI-C" function e_shortreal_2d1;
   export "DPI-C" function e_shortreal_3d1;
`endif

   export "DPI-C" function e_chandle_0d;
   export "DPI-C" function e_chandle_1d;
   export "DPI-C" function e_chandle_2d;
   export "DPI-C" function e_chandle_3d;
   export "DPI-C" function e_chandle_1d1;
   export "DPI-C" function e_chandle_2d1;
   export "DPI-C" function e_chandle_3d1;

   export "DPI-C" function e_string_0d;
   export "DPI-C" function e_string_1d;
   export "DPI-C" function e_string_2d;
   export "DPI-C" function e_string_3d;
   export "DPI-C" function e_string_1d1;
   export "DPI-C" function e_string_2d1;
   export "DPI-C" function e_string_3d1;

   export "DPI-C" function e_bit1_0d;
   export "DPI-C" function e_bit1_1d;
   export "DPI-C" function e_bit1_2d;
   export "DPI-C" function e_bit1_3d;
   export "DPI-C" function e_bit1_1d1;
   export "DPI-C" function e_bit1_2d1;
   export "DPI-C" function e_bit1_3d1;

   export "DPI-C" function e_bit7_0d;
   export "DPI-C" function e_bit7_1d;
   export "DPI-C" function e_bit7_2d;
   export "DPI-C" function e_bit7_3d;
   export "DPI-C" function e_bit7_1d1;
   export "DPI-C" function e_bit7_2d1;
   export "DPI-C" function e_bit7_3d1;

   export "DPI-C" function e_bit121_0d;
   export "DPI-C" function e_bit121_1d;
   export "DPI-C" function e_bit121_2d;
   export "DPI-C" function e_bit121_3d;
   export "DPI-C" function e_bit121_1d1;
   export "DPI-C" function e_bit121_2d1;
   export "DPI-C" function e_bit121_3d1;

   export "DPI-C" function e_logic1_0d;
   export "DPI-C" function e_logic1_1d;
   export "DPI-C" function e_logic1_2d;
   export "DPI-C" function e_logic1_3d;
   export "DPI-C" function e_logic1_1d1;
   export "DPI-C" function e_logic1_2d1;
   export "DPI-C" function e_logic1_3d1;

   export "DPI-C" function e_logic7_0d;
   export "DPI-C" function e_logic7_1d;
   export "DPI-C" function e_logic7_2d;
   export "DPI-C" function e_logic7_3d;
   export "DPI-C" function e_logic7_1d1;
   export "DPI-C" function e_logic7_2d1;
   export "DPI-C" function e_logic7_3d1;

   export "DPI-C" function e_logic121_0d;
   export "DPI-C" function e_logic121_1d;
   export "DPI-C" function e_logic121_2d;
   export "DPI-C" function e_logic121_3d;
   export "DPI-C" function e_logic121_1d1;
   export "DPI-C" function e_logic121_2d1;
   export "DPI-C" function e_logic121_3d1;

   export "DPI-C" function e_pack_struct_0d;
   export "DPI-C" function e_pack_struct_1d;
   export "DPI-C" function e_pack_struct_2d;
   export "DPI-C" function e_pack_struct_3d;
   export "DPI-C" function e_pack_struct_1d1;
   export "DPI-C" function e_pack_struct_2d1;
   export "DPI-C" function e_pack_struct_3d1;

`ifndef NO_UNPACK_STRUCT
   export "DPI-C" function e_unpack_struct_0d;
   export "DPI-C" function e_unpack_struct_1d;
   export "DPI-C" function e_unpack_struct_2d;
   export "DPI-C" function e_unpack_struct_3d;
   export "DPI-C" function e_unpack_struct_1d1;
   export "DPI-C" function e_unpack_struct_2d1;
   export "DPI-C" function e_unpack_struct_3d1;
`endif

   //======================================================================
   // Definitions of exported functions
   //======================================================================
   function void e_byte_0d(input byte val); `CHECK_0D(val); endfunction
   function void e_byte_1d(input byte val[2]); `CHECK_1D(val); endfunction
   function void e_byte_2d(input byte val[3][2]); `CHECK_2D(val); endfunction
   function void e_byte_3d(input byte_array_t val); `CHECK_3D(val); endfunction
   function void e_byte_1d1(input byte val[1]); `CHECK_1D1(val); endfunction
   function void e_byte_2d1(input byte val[1][1]); `CHECK_2D1(val); endfunction
   function void e_byte_3d1(input byte_array1_t val); `CHECK_3D1(val); endfunction

   function void e_byte_unsigned_0d(input byte unsigned val); `CHECK_0D(val); endfunction
   function void e_byte_unsigned_1d(input byte unsigned val[2]); `CHECK_1D(val); endfunction
   function void e_byte_unsigned_2d(input byte unsigned val[3][2]); `CHECK_2D(val); endfunction
   function void e_byte_unsigned_3d(input byte_unsigned_array_t val); `CHECK_3D(val); endfunction
   function void e_byte_unsigned_1d1(input byte unsigned val[1]); `CHECK_1D1(val); endfunction
   function void e_byte_unsigned_2d1(input byte unsigned val[1][1]); `CHECK_2D1(val); endfunction
   function void e_byte_unsigned_3d1(input byte_unsigned_array1_t val); `CHECK_3D1(val); endfunction

   function void e_shortint_0d(input shortint val); `CHECK_0D(val); endfunction
   function void e_shortint_1d(input shortint val[2]); `CHECK_1D(val); endfunction
   function void e_shortint_2d(input shortint val[3][2]); `CHECK_2D(val); endfunction
   function void e_shortint_3d(input shortint_array_t val); `CHECK_3D(val); endfunction
   function void e_shortint_1d1(input shortint val[1]); `CHECK_1D1(val); endfunction
   function void e_shortint_2d1(input shortint val[1][1]); `CHECK_2D1(val); endfunction
   function void e_shortint_3d1(input shortint_array1_t val); `CHECK_3D1(val); endfunction

   function void e_shortint_unsigned_0d(input shortint unsigned val); `CHECK_0D(val); endfunction
   function void e_shortint_unsigned_1d(input shortint unsigned val[2]); `CHECK_1D(val); endfunction
   function void e_shortint_unsigned_2d(input shortint unsigned val[3][2]); `CHECK_2D(val); endfunction
   function void e_shortint_unsigned_3d(input shortint_unsigned_array_t val); `CHECK_3D(val); endfunction
   function void e_shortint_unsigned_1d1(input shortint unsigned val[1]); `CHECK_1D1(val); endfunction
   function void e_shortint_unsigned_2d1(input shortint unsigned val[1][1]); `CHECK_2D1(val); endfunction
   function void e_shortint_unsigned_3d1(input shortint_unsigned_array1_t val); `CHECK_3D1(val); endfunction

   function void e_int_0d(input int val); `CHECK_0D(val); endfunction
   function void e_int_1d(input int val[2]); `CHECK_1D(val); endfunction
   function void e_int_2d(input int val[3][2]); `CHECK_2D(val); endfunction
   function void e_int_3d(input int_array_t val); `CHECK_3D(val); endfunction
   function void e_int_1d1(input int val[1]); `CHECK_1D1(val); endfunction
   function void e_int_2d1(input int val[1][1]); `CHECK_2D1(val); endfunction
   function void e_int_3d1(input int_array1_t val); `CHECK_3D1(val); endfunction

   function void e_int_unsigned_0d(input int unsigned val); `CHECK_0D(val); endfunction
   function void e_int_unsigned_1d(input int unsigned val[2]); `CHECK_1D(val); endfunction
   function void e_int_unsigned_2d(input int unsigned val[3][2]); `CHECK_2D(val); endfunction
   function void e_int_unsigned_3d(input int_unsigned_array_t val); `CHECK_3D(val); endfunction
   function void e_int_unsigned_1d1(input int unsigned val[1]); `CHECK_1D1(val); endfunction
   function void e_int_unsigned_2d1(input int unsigned val[1][1]); `CHECK_2D1(val); endfunction
   function void e_int_unsigned_3d1(input int_unsigned_array1_t val); `CHECK_3D1(val); endfunction

   function void e_longint_0d(input longint val); `CHECK_0D(val); endfunction
   function void e_longint_1d(input longint val[2]); `CHECK_1D(val); endfunction
   function void e_longint_2d(input longint val[3][2]); `CHECK_2D(val); endfunction
   function void e_longint_3d(input longint_array_t val); `CHECK_3D(val); endfunction
   function void e_longint_1d1(input longint val[1]); `CHECK_1D1(val); endfunction
   function void e_longint_2d1(input longint val[1][1]); `CHECK_2D1(val); endfunction
   function void e_longint_3d1(input longint_array1_t val); `CHECK_3D1(val); endfunction

   function void e_longint_unsigned_0d(input longint unsigned val); `CHECK_0D(val); endfunction
   function void e_longint_unsigned_1d(input longint unsigned val[2]); `CHECK_1D(val); endfunction
   function void e_longint_unsigned_2d(input longint unsigned val[3][2]); `CHECK_2D(val); endfunction
   function void e_longint_unsigned_3d(input longint_unsigned_array_t val); `CHECK_3D(val); endfunction
   function void e_longint_unsigned_1d1(input longint unsigned val[1]); `CHECK_1D1(val); endfunction
   function void e_longint_unsigned_2d1(input longint unsigned val[1][1]); `CHECK_2D1(val); endfunction
   function void e_longint_unsigned_3d1(input longint_unsigned_array1_t val); `CHECK_3D1(val); endfunction

`ifndef NO_TIME
   function void e_time_0d(input time val); `CHECK_0D(val); endfunction
   function void e_time_1d(input time val[2]); `CHECK_1D(val); endfunction
   function void e_time_2d(input time val[3][2]); `CHECK_2D(val); endfunction
   function void e_time_3d(input time_array_t val); `CHECK_3D(val); endfunction
   function void e_time_1d1(input time val[1]); `CHECK_1D1(val); endfunction
   function void e_time_2d1(input time val[1][1]); `CHECK_2D1(val); endfunction
   function void e_time_3d1(input time_array1_t val); `CHECK_3D1(val); endfunction
`endif

`ifndef NO_INTEGER
   function void e_integer_0d(input integer val); `CHECK_0D(val); endfunction
   function void e_integer_1d(input integer val[2]); `CHECK_1D(val); endfunction
   function void e_integer_2d(input integer val[3][2]); `CHECK_2D(val); endfunction
   function void e_integer_3d(input integer_array_t val); `CHECK_3D(val); endfunction
   function void e_integer_1d1(input integer val[1]); `CHECK_1D1(val); endfunction
   function void e_integer_2d1(input integer val[1][1]); `CHECK_2D1(val); endfunction
   function void e_integer_3d1(input integer_array1_t val); `CHECK_3D1(val); endfunction
`endif

   function void e_real_0d(input real val); `CHECK_0D(val); endfunction
   function void e_real_1d(input real val[2]); `CHECK_1D(val); endfunction
   function void e_real_2d(input real val[3][2]); `CHECK_2D(val); endfunction
   function void e_real_3d(input real_array_t val); `CHECK_3D(val); endfunction
   function void e_real_1d1(input real val[1]); `CHECK_1D1(val); endfunction
   function void e_real_2d1(input real val[1][1]); `CHECK_2D1(val); endfunction
   function void e_real_3d1(input real_array1_t val); `CHECK_3D1(val); endfunction

`ifndef NO_SHORTREAL
   function void e_shortreal_0d(input shortreal val); `CHECK_0D(val); endfunction
   function void e_shortreal_1d(input shortreal val[2]); `CHECK_1D(val); endfunction
   function void e_shortreal_2d(input shortreal val[3][2]); `CHECK_2D(val); endfunction
   function void e_shortreal_3d(input shortreal_array_t val); `CHECK_3D(val); endfunction
   function void e_shortreal_1d1(input shortreal val[1]); `CHECK_1D1(val); endfunction
   function void e_shortreal_2d1(input shortreal val[1][1]); `CHECK_2D1(val); endfunction
   function void e_shortreal_3d1(input shortreal_array1_t val); `CHECK_3D1(val); endfunction
`endif

   function void e_chandle_0d(input chandle val);
      if (val == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction
   function void e_chandle_1d(input chandle val[2]);
      if (val[0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
      if (val[1] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction
   function void e_chandle_2d(input chandle val[3][2]);
      if (val[0][1] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
      if (val[1][1] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
      if (val[2][1] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction
   function void e_chandle_3d(input chandle_array_t val);
      if (val[0][0][0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
      if (val[1][0][0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
      if (val[2][0][0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
      if (val[3][0][0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction
   function void e_chandle_1d1(input chandle val[1]);
      if (val[0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction
   function void e_chandle_2d1(input chandle val[1][1]);
      if (val[0][0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction
   function void e_chandle_3d1(input chandle_array1_t val);
      if (val[0][0][0] == null) begin
         $display("Mismatch non null is expected, but not.");
         $stop;
      end
   endfunction

   function void e_string_0d(input string val);
      if (val != "42") begin
         $display("Mismatch expected:%s actual:%s", "42", val);
         $stop;
      end
   endfunction
   function void e_string_1d(input string val[2]);
      if (val[0] != "43") begin
         $display("Mismatch expected:%s actual:%s", "43", val[0]);
         $stop;
      end
      if (val[1] != "44") begin
         $display("Mismatch expected:%s actual:%s", "44", val[1]);
         $stop;
      end
   endfunction
   function void e_string_2d(input string val[3][2]);
      if (val[0][1] != "45") begin
         $display("Mismatch expected:%s actual:%s", "45", val[0][1]);
         $stop;
      end
      if (val[1][1] != "46") begin
         $display("Mismatch expected:%s actual:%s", "46", val[1][1]);
         $stop;
      end
      if (val[2][1] != "47") begin
         $display("Mismatch expected:%s actual:%s", "47", val[2][1]);
         $stop;
      end
   endfunction
   function void e_string_3d(input string_array_t val);
      if (val[0][0][0] != "48") begin
         $display("Mismatch expected:%s actual:%s", "48", val[0][0][0]);
         $stop;
      end
      if (val[1][0][0] != "49") begin
         $display("Mismatch expected:%s actual:%s", "49", val[1][0][0]);
         $stop;
      end
      if (val[2][0][0] != "50") begin
         $display("Mismatch expected:%s actual:%s", "50", val[2][0][0]);
         $stop;
      end
      if (val[3][0][0] != "51") begin
         $display("Mismatch expected:%s actual:%s", "51", val[3][0][0]);
         $stop;
      end
   endfunction
   function void e_string_1d1(input string val[1]);
      if (val[0] != "52") begin
         $display("Mismatch expected:%s actual:%s", "52", val[0]);
         $stop;
      end
   endfunction
   function void e_string_2d1(input string val[1][1]);
      if (val[0][0] != "53") begin
         $display("Mismatch expected:%s actual:%s", "53", val[0][0]);
         $stop;
      end
   endfunction
   function void e_string_3d1(input string_array1_t val);
      if (val[0][0][0] != "54") begin
         $display("Mismatch expected:%s actual:%s", "54", val[0][0][0]);
         $stop;
      end
   endfunction

   function void e_bit1_0d(input bit val); `CHECK_0D(val); endfunction
   function void e_bit1_1d(input bit val[2]); `CHECK_1D(val); endfunction
   function void e_bit1_2d(input bit val[3][2]); `CHECK_2D(val); endfunction
   function void e_bit1_3d(input bit1_array_t val); `CHECK_3D(val); endfunction
   function void e_bit1_1d1(input bit val[1]); `CHECK_1D1(val); endfunction
   function void e_bit1_2d1(input bit val[1][1]); `CHECK_2D1(val); endfunction
   function void e_bit1_3d1(input bit1_array1_t val); `CHECK_3D1(val); endfunction

   function void e_bit7_0d(input bit[6:0] val); `CHECK_0D(val); endfunction
   function void e_bit7_1d(input bit[6:0] val[2]); `CHECK_1D(val); endfunction
   function void e_bit7_2d(input bit[6:0] val[3][2]); `CHECK_2D(val); endfunction
   function void e_bit7_3d(input bit7_array_t val); `CHECK_3D(val); endfunction
   function void e_bit7_1d1(input bit[6:0] val[1]); `CHECK_1D1(val); endfunction
   function void e_bit7_2d1(input bit[6:0] val[1][1]); `CHECK_2D1(val); endfunction
   function void e_bit7_3d1(input bit7_array1_t val); `CHECK_3D1(val); endfunction

   function void e_bit121_0d(input bit[120:0] val); `CHECK_0D(val); endfunction
   function void e_bit121_1d(input bit[120:0] val[2]); `CHECK_1D(val); endfunction
   function void e_bit121_2d(input bit[120:0] val[3][2]); `CHECK_2D(val); endfunction
   function void e_bit121_3d(input bit121_array_t val); `CHECK_3D(val); endfunction
   function void e_bit121_1d1(input bit[120:0] val[1]); `CHECK_1D1(val); endfunction
   function void e_bit121_2d1(input bit[120:0] val[1][1]); `CHECK_2D1(val); endfunction
   function void e_bit121_3d1(input bit121_array1_t val); `CHECK_3D1(val); endfunction

   function void e_logic1_0d(input logic val); `CHECK_0D(val); endfunction
   function void e_logic1_1d(input logic val[2]); `CHECK_1D(val); endfunction
   function void e_logic1_2d(input logic val[3][2]); `CHECK_2D(val); endfunction
   function void e_logic1_3d(input logic1_array_t val); `CHECK_3D(val); endfunction
   function void e_logic1_1d1(input logic val[1]); `CHECK_1D1(val); endfunction
   function void e_logic1_2d1(input logic val[1][1]); `CHECK_2D1(val); endfunction
   function void e_logic1_3d1(input logic1_array1_t val); `CHECK_3D1(val); endfunction

   function void e_logic7_0d(input logic[6:0] val); `CHECK_0D(val); endfunction
   function void e_logic7_1d(input logic[6:0] val[2]); `CHECK_1D(val); endfunction
   function void e_logic7_2d(input logic[6:0] val[3][2]); `CHECK_2D(val); endfunction
   function void e_logic7_3d(input logic7_array_t val); `CHECK_3D(val); endfunction
   function void e_logic7_1d1(input logic[6:0] val[1]); `CHECK_1D1(val); endfunction
   function void e_logic7_2d1(input logic[6:0] val[1][1]); `CHECK_2D1(val); endfunction
   function void e_logic7_3d1(input logic7_array1_t val); `CHECK_3D1(val); endfunction

   function void e_logic121_0d(input logic[120:0] val); `CHECK_0D(val); endfunction
   function void e_logic121_1d(input logic[120:0] val[2]); `CHECK_1D(val); endfunction
   function void e_logic121_2d(input logic[120:0] val[3][2]); `CHECK_2D(val); endfunction
   function void e_logic121_3d(input logic121_array_t val); `CHECK_3D(val); endfunction
   function void e_logic121_1d1(input logic[120:0] val[1]); `CHECK_1D1(val); endfunction
   function void e_logic121_2d1(input logic[120:0] val[1][1]); `CHECK_2D1(val); endfunction
   function void e_logic121_3d1(input logic121_array1_t val); `CHECK_3D1(val); endfunction

   function void e_pack_struct_0d(input pack_struct_t val); `CHECK_0D(val); endfunction
   function void e_pack_struct_1d(input pack_struct_t val[2]); `CHECK_1D(val); endfunction
   function void e_pack_struct_2d(input pack_struct_t val[3][2]); `CHECK_2D(val); endfunction
   function void e_pack_struct_3d(input pack_struct_array_t val); `CHECK_3D(val); endfunction
   function void e_pack_struct_1d1(input pack_struct_t val[1]); `CHECK_1D1(val); endfunction
   function void e_pack_struct_2d1(input pack_struct_t val[1][1]); `CHECK_2D1(val); endfunction
   function void e_pack_struct_3d1(input pack_struct_array1_t val); `CHECK_3D1(val); endfunction

`ifndef NO_UNPACK_STRUCT
   function void e_unpack_struct_0d(input unpack_struct_t val);
      if (val.val != 42) begin
         $display("Mismatch expected:%s actual:%s", "42", val.val);
         $stop;
      end
   endfunction
   function void e_unpack_struct_1d(input unpack_struct_t val[2]);
      if (val[0].val != 43) begin
         $display("Mismatch expected:%s actual:%s", "43", val[0].val);
         $stop;
      end
      if (val[1].val != 44) begin
         $display("Mismatch expected:%s actual:%s", "44", val[1].val);
         $stop;
      end
   endfunction
   function void e_unpack_struct_2d(input unpack_struct_t val[3][2]);
      if (val[0][1].val != 45) begin
         $display("Mismatch expected:%s actual:%s", "45", val[0][1].val);
         $stop;
      end
      if (val[1][1].val != 46) begin
         $display("Mismatch expected:%s actual:%s", "46", val[1][1].val);
         $stop;
      end
      if (val[2][1].val != 47) begin
         $display("Mismatch expected:%s actual:%s", "47", val[2][1].val);
         $stop;
      end
   endfunction
   function void e_unpack_struct_3d(input unpack_struct_array_t val);
      if (val[0][0][0].val != 48) begin
         $display("Mismatch expected:%s actual:%s", "48", val[0][0][0].val);
         $stop;
      end
      if (val[1][0][0].val != 49) begin
         $display("Mismatch expected:%s actual:%s", "49", val[1][0][0].val);
         $stop;
      end
      if (val[2][0][0].val != 50) begin
         $display("Mismatch expected:%s actual:%s", "50", val[2][0][0].val);
         $stop;
      end
      if (val[3][0][0].val != 51) begin
         $display("Mismatch expected:%s actual:%s", "51", val[3][0][0].val);
         $stop;
      end
   endfunction
   function void e_unpack_struct_1d1(input unpack_struct_t val[1]);
      if (val[0].val != 52) begin
         $display("Mismatch expected:%s actual:%s", "52", val[0].val);
         $stop;
      end
   endfunction
   function void e_unpack_struct_2d1(input unpack_struct_t val[1][1]);
      if (val[0][0].val != 53) begin
         $display("Mismatch expected:%s actual:%s", "53", val[0][0].val);
         $stop;
      end
   endfunction
   function void e_unpack_struct_3d1(input unpack_struct_array1_t val);
      if (val[0][0][0].val != 54) begin
         $display("Mismatch expected:%s actual:%s", "54", val[0][0][0].val);
         $stop;
      end
   endfunction
`endif

   //======================================================================
   // Invoke all imported functions
   //======================================================================

   import "DPI-C" context function void check_exports();

   initial begin
      byte_array_t byte_array;
      byte_array1_t byte_array1;
      byte_unsigned_array_t byte_unsigned_array;
      byte_unsigned_array1_t byte_unsigned_array1;
      shortint_array_t shortint_array;
      shortint_array1_t shortint_array1;
      shortint_unsigned_array_t shortint_unsigned_array;
      shortint_unsigned_array1_t shortint_unsigned_array1;
      int_array_t int_array;
      int_array1_t int_array1;
      int_unsigned_array_t int_unsigned_array;
      int_unsigned_array1_t int_unsigned_array1;
      longint_array_t longint_array;
      longint_array1_t longint_array1;
      longint_unsigned_array_t longint_unsigned_array;
      longint_unsigned_array1_t longint_unsigned_array1;
`ifndef NO_TIME
      time_array_t time_array;
      time_array1_t time_array1;
`endif
`ifndef NO_INTEGER
      integer_array_t integer_array;
      integer_array1_t integer_array1;
`endif
      real_array_t real_array;
      real_array1_t real_array1;
`ifndef NO_SHORTREAL
      shortreal_array_t shortreal_array;
      shortreal_array1_t shortreal_array1;
`endif
      chandle_array_t chandle_array;
      chandle_array1_t chandle_array1;
      string_array_t string_array;
      string_array1_t string_array1;
      bit1_array_t bit1_array;
      bit1_array1_t bit1_array1;
      bit7_array_t bit7_array;
      bit7_array1_t bit7_array1;
      bit121_array_t bit121_array;
      bit121_array1_t bit121_array1;
      logic1_array_t logic1_array;
      logic1_array1_t logic1_array1;
      logic7_array_t logic7_array;
      logic7_array1_t logic7_array1;
      logic121_array_t logic121_array;
      logic121_array1_t logic121_array1;
      pack_struct_array_t pack_struct_array;
      pack_struct_array1_t pack_struct_array1;
`ifndef NO_UNPACK_STRUCT
      unpack_struct_array_t unpack_struct_array;
      unpack_struct_array1_t unpack_struct_array1;
`endif

      `SET_VALUES(byte_array);
      i_byte_0d(byte_array[3][2][1]);
      i_byte_1d(byte_array[2][1]);
      i_byte_2d(byte_array[1]);
      i_byte_3d(byte_array);

      byte_array1[0][0][0] = 52;
      i_byte_1d1(byte_array1[0][0]);
      byte_array1[0][0][0] = 53;
      i_byte_2d1(byte_array1[0]);
      byte_array1[0][0][0] = 54;
      i_byte_3d1(byte_array1);

      `SET_VALUES(byte_unsigned_array);
      i_byte_unsigned_0d(byte_unsigned_array[3][2][1]);
      i_byte_unsigned_1d(byte_unsigned_array[2][1]);
      i_byte_unsigned_2d(byte_unsigned_array[1]);
      i_byte_unsigned_3d(byte_unsigned_array);

      byte_unsigned_array1[0][0][0] = 52;
      i_byte_unsigned_1d1(byte_unsigned_array1[0][0]);
      byte_unsigned_array1[0][0][0] = 53;
      i_byte_unsigned_2d1(byte_unsigned_array1[0]);
      byte_unsigned_array1[0][0][0] = 54;
      i_byte_unsigned_3d1(byte_unsigned_array1);

      `SET_VALUES(shortint_array);
      i_shortint_0d(shortint_array[3][2][1]);
      i_shortint_1d(shortint_array[2][1]);
      i_shortint_2d(shortint_array[1]);
      i_shortint_3d(shortint_array);

      shortint_array1[0][0][0] = 52;
      i_shortint_1d1(shortint_array1[0][0]);
      shortint_array1[0][0][0] = 53;
      i_shortint_2d1(shortint_array1[0]);
      shortint_array1[0][0][0] = 54;
      i_shortint_3d1(shortint_array1);

      `SET_VALUES(shortint_unsigned_array);
      i_shortint_unsigned_0d(shortint_unsigned_array[3][2][1]);
      i_shortint_unsigned_1d(shortint_unsigned_array[2][1]);
      i_shortint_unsigned_2d(shortint_unsigned_array[1]);
      i_shortint_unsigned_3d(shortint_unsigned_array);

      shortint_unsigned_array1[0][0][0] = 52;
      i_shortint_unsigned_1d1(shortint_unsigned_array1[0][0]);
      shortint_unsigned_array1[0][0][0] = 53;
      i_shortint_unsigned_2d1(shortint_unsigned_array1[0]);
      shortint_unsigned_array1[0][0][0] = 54;
      i_shortint_unsigned_3d1(shortint_unsigned_array1);

      `SET_VALUES(int_array);
      i_int_0d(int_array[3][2][1]);
      i_int_1d(int_array[2][1]);
      i_int_2d(int_array[1]);
      i_int_3d(int_array);

      int_array1[0][0][0] = 52;
      i_int_1d1(int_array1[0][0]);
      int_array1[0][0][0] = 53;
      i_int_2d1(int_array1[0]);
      int_array1[0][0][0] = 54;
      i_int_3d1(int_array1);

      `SET_VALUES(int_unsigned_array);
      i_int_unsigned_0d(int_unsigned_array[3][2][1]);
      i_int_unsigned_1d(int_unsigned_array[2][1]);
      i_int_unsigned_2d(int_unsigned_array[1]);
      i_int_unsigned_3d(int_unsigned_array);

      int_unsigned_array1[0][0][0] = 52;
      i_int_unsigned_1d1(int_unsigned_array1[0][0]);
      int_unsigned_array1[0][0][0] = 53;
      i_int_unsigned_2d1(int_unsigned_array1[0]);
      int_unsigned_array1[0][0][0] = 54;
      i_int_unsigned_3d1(int_unsigned_array1);

      `SET_VALUES(longint_array);
      i_longint_0d(longint_array[3][2][1]);
      i_longint_1d(longint_array[2][1]);
      i_longint_2d(longint_array[1]);
      i_longint_3d(longint_array);

      longint_array1[0][0][0] = 52;
      i_longint_1d1(longint_array1[0][0]);
      longint_array1[0][0][0] = 53;
      i_longint_2d1(longint_array1[0]);
      longint_array1[0][0][0] = 54;
      i_longint_3d1(longint_array1);

      `SET_VALUES(longint_unsigned_array);
      i_longint_unsigned_0d(longint_unsigned_array[3][2][1]);
      i_longint_unsigned_1d(longint_unsigned_array[2][1]);
      i_longint_unsigned_2d(longint_unsigned_array[1]);
      i_longint_unsigned_3d(longint_unsigned_array);

      longint_unsigned_array1[0][0][0] = 52;
      i_longint_unsigned_1d1(longint_unsigned_array1[0][0]);
      longint_unsigned_array1[0][0][0] = 53;
      i_longint_unsigned_2d1(longint_unsigned_array1[0]);
      longint_unsigned_array1[0][0][0] = 54;
      i_longint_unsigned_3d1(longint_unsigned_array1);

`ifndef NO_TIME
      `SET_VALUES(time_array);
      i_time_0d(time_array[3][2][1]);
      i_time_1d(time_array[2][1]);
      i_time_2d(time_array[1]);
      i_time_3d(time_array);

      time_array1[0][0][0] = 52;
      i_time_1d1(time_array1[0][0]);
      time_array1[0][0][0] = 53;
      i_time_2d1(time_array1[0]);
      time_array1[0][0][0] = 54;
      i_time_3d1(time_array1);
`endif

`ifndef NO_INTEGER
      `SET_VALUES(integer_array);
      i_integer_0d(integer_array[3][2][1]);
      i_integer_1d(integer_array[2][1]);
      i_integer_2d(integer_array[1]);
      i_integer_3d(integer_array);

      integer_array1[0][0][0] = 52;
      i_integer_1d1(integer_array1[0][0]);
      integer_array1[0][0][0] = 53;
      i_integer_2d1(integer_array1[0]);
      integer_array1[0][0][0] = 54;
      i_integer_3d1(integer_array1);
`endif

      `SET_VALUES(real_array);
      i_real_0d(real_array[3][2][1]);
      i_real_1d(real_array[2][1]);
      i_real_2d(real_array[1]);
      i_real_3d(real_array);

      real_array1[0][0][0] = 52;
      i_real_1d1(real_array1[0][0]);
      real_array1[0][0][0] = 53;
      i_real_2d1(real_array1[0]);
      real_array1[0][0][0] = 54;
      i_real_3d1(real_array1);

`ifndef NO_SHORTREAL
      `SET_VALUES(shortreal_array);
      i_shortreal_0d(shortreal_array[3][2][1]);
      i_shortreal_1d(shortreal_array[2][1]);
      i_shortreal_2d(shortreal_array[1]);
      i_shortreal_3d(shortreal_array);

      shortreal_array1[0][0][0] = 52;
      i_shortreal_1d1(shotreal_array1[0][0]);
      shortreal_array1[0][0][0] = 53;
      i_shortreal_2d1(shotreal_array1[0]);
      shortreal_array1[0][0][0] = 54;
      i_shortreal_3d1(shotreal_array1);
`endif

      for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 3; ++j)
          for (int k = 0; k < 2; ++k)
            chandle_array[i][j][k] = null;

      chandle_array[3][2][1] = get_non_null();
      i_chandle_0d(chandle_array[3][2][1]);
      chandle_array[2][1][0] = get_non_null();
      chandle_array[2][1][1] = get_non_null();
      i_chandle_1d(chandle_array[2][1]);
      chandle_array[1][0][1] = get_non_null();
      chandle_array[1][1][1] = get_non_null();
      chandle_array[1][2][1] = get_non_null();
      i_chandle_2d(chandle_array[1]);
      chandle_array[0][0][0] = get_non_null();
      chandle_array[1][0][0] = get_non_null();
      chandle_array[2][0][0] = get_non_null();
      chandle_array[3][0][0] = get_non_null();
      i_chandle_3d(chandle_array);

      chandle_array1[0][0][0] = get_non_null();
      i_chandle_1d1(chandle_array1[0][0]);
      chandle_array1[0][0][0] = get_non_null();
      i_chandle_2d1(chandle_array1[0]);
      chandle_array1[0][0][0] = get_non_null();
      i_chandle_3d1(chandle_array1);

      string_array[3][2][1] = "42";
      string_array[2][1][0] = "43"; string_array[2][1][1] = "44";
      string_array[1][0][1] = "45"; string_array[1][1][1] = "46"; string_array[1][2][1] = "47";
      string_array[0][0][0] = "48"; string_array[1][0][0] = "49"; string_array[2][0][0] = "50"; string_array[3][0][0] = "51";
      i_string_0d(string_array[3][2][1]);
      i_string_1d(string_array[2][1]);
      i_string_2d(string_array[1]);
      i_string_3d(string_array);

      string_array1[0][0][0] = "52";
      i_string_1d1(string_array1[0][0]);
      string_array1[0][0][0] = "53";
      i_string_2d1(string_array1[0]);
      string_array1[0][0][0] = "54";
      i_string_3d1(string_array1);

      `SET_VALUES(bit1_array);
      i_bit1_0d(bit1_array[3][2][1]);
      i_bit1_1d(bit1_array[2][1]);
      i_bit1_2d(bit1_array[1]);
      i_bit1_3d(bit1_array);

      bit1_array1[0][0][0] = 1'(52);
      i_bit1_1d1(bit1_array1[0][0]);
      bit1_array1[0][0][0] = 1'(53);
      i_bit1_2d1(bit1_array1[0]);
      bit1_array1[0][0][0] = 1'(54);
      i_bit1_3d1(bit1_array1);

      `SET_VALUES(bit7_array);
      i_bit7_0d(bit7_array[3][2][1]);
      i_bit7_1d(bit7_array[2][1]);
      i_bit7_2d(bit7_array[1]);
      i_bit7_3d(bit7_array);

      bit7_array1[0][0][0] = 52;
      i_bit7_1d1(bit7_array1[0][0]);
      bit7_array1[0][0][0] = 53;
      i_bit7_2d1(bit7_array1[0]);
      bit7_array1[0][0][0] = 54;
      i_bit7_3d1(bit7_array1);

      `SET_VALUES(bit121_array);
      i_bit121_0d(bit121_array[3][2][1]);
      i_bit121_1d(bit121_array[2][1]);
      i_bit121_2d(bit121_array[1]);
      i_bit121_3d(bit121_array);

      bit121_array1[0][0][0] = 52;
      i_bit121_1d1(bit121_array1[0][0]);
      bit121_array1[0][0][0] = 53;
      i_bit121_2d1(bit121_array1[0]);
      bit121_array1[0][0][0] = 54;
      i_bit121_3d1(bit121_array1);

      `SET_VALUES(logic1_array);
      i_logic1_0d(logic1_array[3][2][1]);
      i_logic1_1d(logic1_array[2][1]);
      i_logic1_2d(logic1_array[1]);
      i_logic1_3d(logic1_array);

      logic1_array1[0][0][0] = 1'(52);
      i_logic1_1d1(logic1_array1[0][0]);
      logic1_array1[0][0][0] = 1'(53);
      i_logic1_2d1(logic1_array1[0]);
      logic1_array1[0][0][0] = 1'(54);
      i_logic1_3d1(logic1_array1);

      `SET_VALUES(logic7_array);
      i_logic7_0d(logic7_array[3][2][1]);
      i_logic7_1d(logic7_array[2][1]);
      i_logic7_2d(logic7_array[1]);
      i_logic7_3d(logic7_array);

      logic7_array1[0][0][0] = 52;
      i_logic7_1d1(logic7_array1[0][0]);
      logic7_array1[0][0][0] = 53;
      i_logic7_2d1(logic7_array1[0]);
      logic7_array1[0][0][0] = 54;
      i_logic7_3d1(logic7_array1);

      `SET_VALUES(logic121_array);
      i_logic121_0d(logic121_array[3][2][1]);
      i_logic121_1d(logic121_array[2][1]);
      i_logic121_2d(logic121_array[1]);
      i_logic121_3d(logic121_array);

      logic121_array1[0][0][0] = 52;
      i_logic121_1d1(logic121_array1[0][0]);
      logic121_array1[0][0][0] = 53;
      i_logic121_2d1(logic121_array1[0]);
      logic121_array1[0][0][0] = 54;
      i_logic121_3d1(logic121_array1);

      `SET_VALUES(pack_struct_array);
      i_pack_struct_0d(pack_struct_array[3][2][1]);
      i_pack_struct_1d(pack_struct_array[2][1]);
      i_pack_struct_2d(pack_struct_array[1]);
      i_pack_struct_3d(pack_struct_array);

      pack_struct_array1[0][0][0] = 52;
      i_pack_struct_1d1(pack_struct_array1[0][0]);
      pack_struct_array1[0][0][0] = 53;
      i_pack_struct_2d1(pack_struct_array1[0]);
      pack_struct_array1[0][0][0] = 54;
      i_pack_struct_3d1(pack_struct_array1);

`ifndef NO_UNPACK_STRUCT
      unpack_struct_array[3][2][1].val = 42;
      unpack_struct_array[2][1][0].val = 43;
      unpack_struct_array[2][1][1].val = 44;

      unpack_struct_array[1][0][1].val = 45;
      unpack_struct_array[1][1][1].val = 46;
      unpack_struct_array[1][2][1].val = 47;

      unpack_struct_array[0][0][0].val = 48;
      unpack_struct_array[1][0][0].val = 49;
      unpack_struct_array[2][0][0].val = 50;
      unpack_struct_array[3][0][0].val = 51;
      i_unpack_struct_0d(unpack_struct_array[3][2][1]);
      i_unpack_struct_1d(unpack_struct_array[2][1]);
      i_unpack_struct_2d(unpack_struct_array[1]);
      i_unpack_struct_3d(unpack_struct_array);

      unpack_struct_array1[0][0][0].val = 52;
      i_unpack_struct_1d1(unpack_struct_array1[0][0]);
      unpack_struct_array1[0][0][0].val = 53;
      i_unpack_struct_2d1(unpack_struct_array1[0]);
      unpack_struct_array1[0][0][0].val = 54;
      i_unpack_struct_3d1(unpack_struct_array1);
`endif

      check_exports();

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
