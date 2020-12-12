// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Yutetsu TAKATSUKASA. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
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
//%Error-TASKNSVAR: Unsupported: Function/task input argument is not simple variable
 `define NO_INOUT_COMPLEX_TYPE
`endif

`ifdef NO_BITS_TO_SCALAR
 `define ARE_SAME(act, exp) ($bits((act)) == 1 ? (act) == ((exp) & 1) : (act) == (exp))
`else
 `define ARE_SAME(act, exp) ((act) == (($bits(act))'(exp)))
`endif

`define CHECK_VAL(act, exp) if (`ARE_SAME(act, exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":", (act), " as expected"); \
     end else begin \
        $display("Mismatch %s expected:%d actual:%d at %d", `"act`", int'(exp), int'(act), `__LINE__); \
          $stop; \
            end

`define CHECK_CHANDLE_VAL(act, exp) if ((act) == (exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":non-null as expected"); \
     end else begin \
        $display("Mismatch %s expected:%s but %s at %d", `"act`", \
                 (exp) != null ? "null" : "non-null", \
                 (act) != null ? "null" : "non-null", `__LINE__); \
                          $stop; \
                          end

`define CHECK_STRING_VAL(act, exp) if ((act) == (exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":", (act), " as expected"); \
     end else begin \
        $display("Mismatch %s expected:%s actual:%s at %d", `"act`", (exp), (act), `__LINE__); \
          $stop; \
            end

`define UPDATE_VAL(var, val) `CHECK_VAL(var, val); var += 1
`define UPDATE_0D(val) `UPDATE_VAL(val, 42)
`define UPDATE_1D(val) `UPDATE_VAL(val[0], 43); \
`UPDATE_VAL(val[1], 44)
`define UPDATE_2D(val) `UPDATE_VAL(val[0][1], 45); \
`UPDATE_VAL(val[1][1], 46); \
`UPDATE_VAL(val[2][1], 47)
`define UPDATE_3D(val) `UPDATE_VAL(val[0][0][0], 48); \
`UPDATE_VAL(val[1][0][0], 49); \
`UPDATE_VAL(val[2][0][0], 50); \
`UPDATE_VAL(val[3][0][0], 51)

`define CHECK_0D(val) `CHECK_VAL((val), 43)
`define CHECK_1D(val) `CHECK_VAL(val[0], 44); \
`CHECK_VAL(val[1], 45)
`define CHECK_2D(val) `CHECK_VAL(val[0][1], 46); \
`CHECK_VAL(val[1][1], 47); `CHECK_VAL(val[2][1], 48)
`define CHECK_3D(val) `CHECK_VAL(val[0][0][0], 49); \
`CHECK_VAL(val[1][0][0], 50); \
`CHECK_VAL(val[2][0][0], 51); \
`CHECK_VAL(val[3][0][0], 52)

`define CHECK_DOUBLE_VAL(act, exp) if ((act) == (exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display("%s:%f as expected", `"act`", (act)); \
     end else begin \
        $display("Mismatch %s expected:%d actual:%f at %f", `"act`", (exp), (act), `__LINE__); \
          $stop; \
            end

`define CHECK_DOUBLE_0D(val) `CHECK_DOUBLE_VAL((val), 43.0)
`define CHECK_DOUBLE_1D(val) `CHECK_DOUBLE_VAL(val[0], 44.0); \
`CHECK_DOUBLE_VAL(val[1], 45.0)
`define CHECK_DOUBLE_2D(val) `CHECK_DOUBLE_VAL(val[0][1], 46.0); \
`CHECK_DOUBLE_VAL(val[1][1], 47.0); \
`CHECK_DOUBLE_VAL(val[2][1], 48.0)
`define CHECK_DOUBLE_3D(val) `CHECK_DOUBLE_VAL(val[0][0][0], 49.0); \
`CHECK_DOUBLE_VAL(val[1][0][0], 50.0); \
`CHECK_DOUBLE_VAL(val[2][0][0], 51.0); \
`CHECK_DOUBLE_VAL(val[3][0][0], 52.0)

`define SET_VALUE_0D(val) \
/*verilator lint_off WIDTH */ \
val = 42
/*verilator lint_on WIDTH */
`define SET_VALUE_1D(val) \
/*verilator lint_off WIDTH */ \
val[0] = 43; val[1] = 44 \
/*verilator lint_on WIDTH */
`define SET_VALUE_2D(val) \
/*verilator lint_off WIDTH */ \
val[0][1] = 45; val[1][1] = 46; val[2][1] = 47 \
/*verilator lint_on WIDTH */
`define SET_VALUES(val) \
/*verilator lint_off WIDTH */ \
val[3][2][1] = 42; \
val[2][1][0] = 43; val[2][1][1] = 44; \
val[1][0][1] = 45; val[1][1][1] = 46; val[1][2][1] = 47; \
val[0][0][0] = 48; val[1][0][0] = 49; val[2][0][0] = 50; val[3][0][0] = 51 \
/*verilator lint_on WIDTH */

module t;

   localparam ENABLE_VERBOSE_MESSAGE = 0;

   // Legal output argument types for DPI functions

   //======================================================================
   // Type definitions
   //======================================================================

   typedef byte byte_t;
   typedef byte_t            byte_array_t[4][3][2];
   typedef byte unsigned byte_unsigned_t;
   typedef byte_unsigned_t   byte_unsigned_array_t[4][3][2];
   typedef shortint      shortint_t;
   typedef shortint_t        shortint_array_t[4][3][2];
   typedef shortint unsigned shortint_unsigned_t;
   typedef shortint_unsigned_t shortint_unsigned_array_t[4][3][2];
   typedef int               int_t;
   typedef int_t             int_array_t[4][3][2];
   typedef int unsigned      int_unsigned_t;
   typedef int_unsigned_t    int_unsigned_array_t[4][3][2];
   typedef longint           longint_t;
   typedef longint_t         longint_array_t[4][3][2];
   typedef longint unsigned  longint_unsigned_t;
   typedef longint_unsigned_t longint_unsigned_array_t[4][3][2];
`ifndef NO_TIME
   typedef time              time_t;
   typedef time_t            time_array_t[4][3][2];
`endif
`ifndef NO_INTEGER
   typedef integer           integer_t;
   typedef integer_t         integer_array_t[4][3][2];
`endif
   typedef real              real_t;
   typedef real_t            real_array_t[4][3][2];
`ifndef NO_SHORTREAL
   typedef shortreal         shortreal_t;
   typedef shortreal_t       shortreal_array_t[4][3][2];
`endif
   typedef chandle           chandle_t;
   typedef chandle_t         chandle_array_t[4][3][2];
   typedef string            string_t;
   typedef string_t          string_array_t[4][3][2];
   typedef bit               bit1_t;
   typedef bit1_t            bit1_array_t[4][3][2];
   typedef bit [6:0]         bit7_t;
   typedef bit7_t            bit7_array_t[4][3][2];
   typedef bit [120:0]       bit121_t;
   typedef bit121_t          bit121_array_t[4][3][2];
   typedef logic             logic1_t;
   typedef logic1_t            logic1_array_t[4][3][2];
   typedef logic [6:0]       logic7_t;
   typedef logic7_t          logic7_array_t[4][3][2];
   typedef logic [120:0]     logic121_t;
   typedef logic121_t        logic121_array_t[4][3][2];

   typedef struct            packed {
      logic [6:0]            val;
   } pack_struct_t;
   typedef pack_struct_t pack_struct_array_t[4][3][2];
`ifndef NO_UNPACK_STRUCT
   typedef struct            {
      logic [120:0]          val;
   } unpack_struct_t;
   typedef unpack_struct_t unpack_struct_array_t[4][3][2];
`endif

   //======================================================================
   // Imports
   //======================================================================

   // Returns non-null pointer
   import "DPI-C" function chandle get_non_null();

   import "DPI-C" function void i_byte_0d(inout byte_t val);
   import "DPI-C" function void i_byte_1d(inout byte_t val[2]);
   import "DPI-C" function void i_byte_2d(inout byte_t val[3][2]);
   import "DPI-C" function void i_byte_3d(inout byte_array_t val);

   import "DPI-C" function void i_byte_unsigned_0d(inout byte unsigned val);
   import "DPI-C" function void i_byte_unsigned_1d(inout byte unsigned val[2]);
   import "DPI-C" function void i_byte_unsigned_2d(inout byte unsigned val[3][2]);
   import "DPI-C" function void i_byte_unsigned_3d(inout byte_unsigned_array_t val);

   import "DPI-C" function void i_shortint_0d(inout shortint val);
   import "DPI-C" function void i_shortint_1d(inout shortint val[2]);
   import "DPI-C" function void i_shortint_2d(inout shortint val[3][2]);
   import "DPI-C" function void i_shortint_3d(inout shortint_array_t val);

   import "DPI-C" function void i_shortint_unsigned_0d(inout shortint unsigned val);
   import "DPI-C" function void i_shortint_unsigned_1d(inout shortint unsigned val[2]);
   import "DPI-C" function void i_shortint_unsigned_2d(inout shortint unsigned val[3][2]);
   import "DPI-C" function void i_shortint_unsigned_3d(inout shortint_unsigned_array_t val);

   import "DPI-C" function void i_int_0d(inout int val);
   import "DPI-C" function void i_int_1d(inout int val[2]);
   import "DPI-C" function void i_int_2d(inout int val[3][2]);
   import "DPI-C" function void i_int_3d(inout int_array_t val);

   import "DPI-C" function void i_int_unsigned_0d(inout int unsigned val);
   import "DPI-C" function void i_int_unsigned_1d(inout int unsigned val[2]);
   import "DPI-C" function void i_int_unsigned_2d(inout int unsigned val[3][2]);
   import "DPI-C" function void i_int_unsigned_3d(inout int_unsigned_array_t val);

   import "DPI-C" function void i_longint_0d(inout longint val);
   import "DPI-C" function void i_longint_1d(inout longint val[2]);
   import "DPI-C" function void i_longint_2d(inout longint val[3][2]);
   import "DPI-C" function void i_longint_3d(inout longint_array_t val);

   import "DPI-C" function void i_longint_unsigned_0d(inout longint unsigned val);
   import "DPI-C" function void i_longint_unsigned_1d(inout longint unsigned val[2]);
   import "DPI-C" function void i_longint_unsigned_2d(inout longint unsigned val[3][2]);
   import "DPI-C" function void i_longint_unsigned_3d(inout longint_unsigned_array_t val);

`ifndef NO_TIME
   import "DPI-C" function void i_time_0d(inout time val);
   import "DPI-C" function void i_time_1d(inout time val[2]);
   import "DPI-C" function void i_time_2d(inout time val[3][2]);
   import "DPI-C" function void i_time_3d(inout time_array_t val);
`endif

`ifndef NO_INTEGER
   import "DPI-C" function void i_integer_0d(inout integer val);
   import "DPI-C" function void i_integer_1d(inout integer val[2]);
   import "DPI-C" function void i_integer_2d(inout integer val[3][2]);
   import "DPI-C" function void i_integer_3d(inout integer_array_t val);
`endif

   import "DPI-C" function void i_real_0d(inout real val);
   import "DPI-C" function void i_real_1d(inout real val[2]);
   import "DPI-C" function void i_real_2d(inout real val[3][2]);
   import "DPI-C" function void i_real_3d(inout real_array_t val);

`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal_0d(inout shortreal val);
   import "DPI-C" function void i_shortreal_1d(inout shortreal val[2]);
   import "DPI-C" function void i_shortreal_2d(inout shortreal val[3][2]);
   import "DPI-C" function void i_shortreal_3d(inout shortreal_array_t val);
`endif

   import "DPI-C" function void i_chandle_0d(inout chandle val);
   import "DPI-C" function void i_chandle_1d(inout chandle val[2]);
   import "DPI-C" function void i_chandle_2d(inout chandle val[3][2]);
   import "DPI-C" function void i_chandle_3d(inout chandle_array_t val);

   import "DPI-C" function void i_string_0d(inout string val);
   import "DPI-C" function void i_string_1d(inout string val[2]);
   import "DPI-C" function void i_string_2d(inout string val[3][2]);
   import "DPI-C" function void i_string_3d(inout string_array_t val);

   import "DPI-C" function void i_bit1_0d(inout bit val);
   import "DPI-C" function void i_bit1_1d(inout bit val[2]);
   import "DPI-C" function void i_bit1_2d(inout bit val[3][2]);
   import "DPI-C" function void i_bit1_3d(inout bit1_array_t val);

   import "DPI-C" function void i_bit7_0d(inout bit[6:0] val);
   import "DPI-C" function void i_bit7_1d(inout bit[6:0] val[2]);
   import "DPI-C" function void i_bit7_2d(inout bit[6:0] val[3][2]);
   import "DPI-C" function void i_bit7_3d(inout bit7_array_t val);

   import "DPI-C" function void i_bit121_0d(inout bit[120:0] val);
   import "DPI-C" function void i_bit121_1d(inout bit[120:0] val[2]);
   import "DPI-C" function void i_bit121_2d(inout bit[120:0] val[3][2]);
   import "DPI-C" function void i_bit121_3d(inout bit121_array_t val);

   import "DPI-C" function void i_logic1_0d(inout logic val);
   import "DPI-C" function void i_logic1_1d(inout logic val[2]);
   import "DPI-C" function void i_logic1_2d(inout logic val[3][2]);
   import "DPI-C" function void i_logic1_3d(inout logic1_array_t val);

   import "DPI-C" function void i_logic7_0d(inout logic[6:0] val);
   import "DPI-C" function void i_logic7_1d(inout logic[6:0] val[2]);
   import "DPI-C" function void i_logic7_2d(inout logic[6:0] val[3][2]);
   import "DPI-C" function void i_logic7_3d(inout logic7_array_t val);

   import "DPI-C" function void i_logic121_0d(inout logic[120:0] val);
   import "DPI-C" function void i_logic121_1d(inout logic[120:0] val[2]);
   import "DPI-C" function void i_logic121_2d(inout logic[120:0] val[3][2]);
   import "DPI-C" function void i_logic121_3d(inout logic121_array_t val);

   import "DPI-C" function void i_pack_struct_0d(inout pack_struct_t val);
   import "DPI-C" function void i_pack_struct_1d(inout pack_struct_t val[2]);
   import "DPI-C" function void i_pack_struct_2d(inout pack_struct_t val[3][2]);
   import "DPI-C" function void i_pack_struct_3d(inout pack_struct_array_t val);

`ifndef NO_UNPACK_STRUCT
   import "DPI-C" function void i_unpack_struct_0d(inout unpack_struct_t val);
   import "DPI-C" function void i_unpack_struct_1d(inout unpack_struct_t val[2]);
   import "DPI-C" function void i_unpack_struct_2d(inout unpack_struct_t val[3][2]);
   import "DPI-C" function void i_unpack_struct_3d(inout unpack_struct_array_t val);
`endif

   //======================================================================
   // Exports
   //======================================================================
   export "DPI-C" function e_byte_0d;
   export "DPI-C" function e_byte_1d;
   export "DPI-C" function e_byte_2d;
   export "DPI-C" function e_byte_3d;

   export "DPI-C" function e_byte_unsigned_0d;
   export "DPI-C" function e_byte_unsigned_1d;
   export "DPI-C" function e_byte_unsigned_2d;
   export "DPI-C" function e_byte_unsigned_3d;

   export "DPI-C" function e_shortint_0d;
   export "DPI-C" function e_shortint_1d;
   export "DPI-C" function e_shortint_2d;
   export "DPI-C" function e_shortint_3d;

   export "DPI-C" function e_shortint_unsigned_0d;
   export "DPI-C" function e_shortint_unsigned_1d;
   export "DPI-C" function e_shortint_unsigned_2d;
   export "DPI-C" function e_shortint_unsigned_3d;

   export "DPI-C" function e_int_0d;
   export "DPI-C" function e_int_1d;
   export "DPI-C" function e_int_2d;
   export "DPI-C" function e_int_3d;

   export "DPI-C" function e_int_unsigned_0d;
   export "DPI-C" function e_int_unsigned_1d;
   export "DPI-C" function e_int_unsigned_2d;
   export "DPI-C" function e_int_unsigned_3d;

   export "DPI-C" function e_longint_0d;
   export "DPI-C" function e_longint_1d;
   export "DPI-C" function e_longint_2d;
   export "DPI-C" function e_longint_3d;

   export "DPI-C" function e_longint_unsigned_0d;
   export "DPI-C" function e_longint_unsigned_1d;
   export "DPI-C" function e_longint_unsigned_2d;
   export "DPI-C" function e_longint_unsigned_3d;

`ifndef NO_TIME
   export "DPI-C" function e_time_0d;
   export "DPI-C" function e_time_1d;
   export "DPI-C" function e_time_2d;
   export "DPI-C" function e_time_3d;
`endif

`ifndef NO_INTEGER
   export "DPI-C" function e_integer_0d;
   export "DPI-C" function e_integer_1d;
   export "DPI-C" function e_integer_2d;
   export "DPI-C" function e_integer_3d;
`endif

   export "DPI-C" function e_real_0d;
   export "DPI-C" function e_real_1d;
   export "DPI-C" function e_real_2d;
   export "DPI-C" function e_real_3d;

`ifndef NO_SHORTREAL
   export "DPI-C" function e_shortreal_0d;
   export "DPI-C" function e_shortreal_1d;
   export "DPI-C" function e_shortreal_2d;
   export "DPI-C" function e_shortreal_3d;
`endif

   export "DPI-C" function e_chandle_0d;
   export "DPI-C" function e_chandle_1d;
   export "DPI-C" function e_chandle_2d;
   export "DPI-C" function e_chandle_3d;

   export "DPI-C" function e_string_0d;
   export "DPI-C" function e_string_1d;
   export "DPI-C" function e_string_2d;
   export "DPI-C" function e_string_3d;

   export "DPI-C" function e_bit1_0d;
   export "DPI-C" function e_bit1_1d;
   export "DPI-C" function e_bit1_2d;
   export "DPI-C" function e_bit1_3d;

   export "DPI-C" function e_bit7_0d;
   export "DPI-C" function e_bit7_1d;
   export "DPI-C" function e_bit7_2d;
   export "DPI-C" function e_bit7_3d;

   export "DPI-C" function e_bit121_0d;
   export "DPI-C" function e_bit121_1d;
   export "DPI-C" function e_bit121_2d;
   export "DPI-C" function e_bit121_3d;

   export "DPI-C" function e_logic1_0d;
   export "DPI-C" function e_logic1_1d;
   export "DPI-C" function e_logic1_2d;
   export "DPI-C" function e_logic1_3d;

   export "DPI-C" function e_logic7_0d;
   export "DPI-C" function e_logic7_1d;
   export "DPI-C" function e_logic7_2d;
   export "DPI-C" function e_logic7_3d;

   export "DPI-C" function e_logic121_0d;
   export "DPI-C" function e_logic121_1d;
   export "DPI-C" function e_logic121_2d;
   export "DPI-C" function e_logic121_3d;

   export "DPI-C" function e_pack_struct_0d;
   export "DPI-C" function e_pack_struct_1d;
   export "DPI-C" function e_pack_struct_2d;
   export "DPI-C" function e_pack_struct_3d;

`ifndef NO_UNPACK_STRUCT
   export "DPI-C" function e_unpack_struct_0d;
   export "DPI-C" function e_unpack_struct_1d;
   export "DPI-C" function e_unpack_struct_2d;
   export "DPI-C" function e_unpack_struct_3d;
`endif
   //======================================================================
   // Definitions of exported functions
   //======================================================================

   function void e_byte_0d(inout byte val); `UPDATE_0D(val); endfunction
   function void e_byte_1d(inout byte val[2]); `UPDATE_1D(val); endfunction
   function void e_byte_2d(inout byte val[3][2]); `UPDATE_2D(val); endfunction
   function void e_byte_3d(inout byte_array_t val); `UPDATE_3D(val); endfunction

   function void e_byte_unsigned_0d(inout byte unsigned val); `UPDATE_0D(val); endfunction
   function void e_byte_unsigned_1d(inout byte unsigned val[2]); `UPDATE_1D(val); endfunction
   function void e_byte_unsigned_2d(inout byte unsigned val[3][2]); `UPDATE_2D(val); endfunction
   function void e_byte_unsigned_3d(inout byte_unsigned_array_t val); `UPDATE_3D(val); endfunction

   function void e_shortint_0d(inout shortint val); `UPDATE_0D(val); endfunction
   function void e_shortint_1d(inout shortint val[2]); `UPDATE_1D(val); endfunction
   function void e_shortint_2d(inout shortint val[3][2]); `UPDATE_2D(val); endfunction
   function void e_shortint_3d(inout shortint_array_t val); `UPDATE_3D(val); endfunction

   function void e_shortint_unsigned_0d(inout shortint unsigned val); `UPDATE_0D(val); endfunction
   function void e_shortint_unsigned_1d(inout shortint unsigned val[2]); `UPDATE_1D(val); endfunction
   function void e_shortint_unsigned_2d(inout shortint unsigned val[3][2]); `UPDATE_2D(val); endfunction
   function void e_shortint_unsigned_3d(inout shortint_unsigned_array_t val); `UPDATE_3D(val); endfunction


   function void e_int_0d(inout int val); `UPDATE_0D(val); endfunction
   function void e_int_1d(inout int val[2]); `UPDATE_1D(val); endfunction
   function void e_int_2d(inout int val[3][2]); `UPDATE_2D(val); endfunction
   function void e_int_3d(inout int_array_t val); `UPDATE_3D(val); endfunction

   function void e_int_unsigned_0d(inout int unsigned val); `UPDATE_0D(val); endfunction
   function void e_int_unsigned_1d(inout int unsigned val[2]); `UPDATE_1D(val); endfunction
   function void e_int_unsigned_2d(inout int unsigned val[3][2]); `UPDATE_2D(val); endfunction
   function void e_int_unsigned_3d(inout int_unsigned_array_t val); `UPDATE_3D(val); endfunction



   function void e_longint_0d(inout longint val); `UPDATE_0D(val); endfunction
   function void e_longint_1d(inout longint val[2]); `UPDATE_1D(val); endfunction
   function void e_longint_2d(inout longint val[3][2]); `UPDATE_2D(val); endfunction
   function void e_longint_3d(inout longint_array_t val); `UPDATE_3D(val); endfunction

   function void e_longint_unsigned_0d(inout longint unsigned val); `UPDATE_0D(val); endfunction
   function void e_longint_unsigned_1d(inout longint unsigned val[2]); `UPDATE_1D(val); endfunction
   function void e_longint_unsigned_2d(inout longint unsigned val[3][2]); `UPDATE_2D(val); endfunction
   function void e_longint_unsigned_3d(inout longint_unsigned_array_t val); `UPDATE_3D(val); endfunction

`ifndef NO_TIME
   function void e_time_0d(inout time val); `UPDATE_0D(val); endfunction
   function void e_time_1d(inout time val[2]); `UPDATE_1D(val); endfunction
   function void e_time_2d(inout time val[3][2]); `UPDATE_2D(val); endfunction
   function void e_time_3d(inout time_array_t val); `UPDATE_3D(val); endfunction
`endif

`ifndef NO_INTEGER
   function void e_integer_0d(inout integer val); `UPDATE_0D(val); endfunction
   function void e_integer_1d(inout integer val[2]); `UPDATE_1D(val); endfunction
   function void e_integer_2d(inout integer val[3][2]); `UPDATE_2D(val); endfunction
   function void e_integer_3d(inout integer_array_t val); `UPDATE_3D(val); endfunction
`endif

   function void e_real_0d(inout real val); `UPDATE_0D(val); endfunction
   function void e_real_1d(inout real val[2]); `UPDATE_1D(val); endfunction
   function void e_real_2d(inout real val[3][2]); `UPDATE_2D(val); endfunction
   function void e_real_3d(inout real_array_t val); `UPDATE_3D(val); endfunction

`ifndef NO_SHORTREAL
   function void e_shortreal_0d(inout shortreal val); `UPDATE_0D(val); endfunction
   function void e_shortreal_1d(inout shortreal val[2]); `UPDATE_1D(val); endfunction
   function void e_shortreal_2d(inout shortreal val[3][2]); `UPDATE_2D(val); endfunction
   function void e_shortreal_3d(inout shortreal_array_t val); `UPDATE_3D(val); endfunction
`endif


   function void e_chandle_0d(inout chandle val);
      `CHECK_CHANDLE_VAL(val, get_non_null());
      val = null;
   endfunction
   function void e_chandle_1d(inout chandle val[2]);
      `CHECK_CHANDLE_VAL(val[0], get_non_null());
      `CHECK_CHANDLE_VAL(val[1], get_non_null());
      val[0] = null;
      val[1] = null;
   endfunction
   function void e_chandle_2d(inout chandle val[3][2]);
      `CHECK_CHANDLE_VAL(val[0][1], get_non_null());
      `CHECK_CHANDLE_VAL(val[1][1], get_non_null());
      `CHECK_CHANDLE_VAL(val[2][1], get_non_null());
      val[0][1] = null;
      val[1][1] = null;
      val[2][1] = null;
   endfunction
   function void e_chandle_3d(inout chandle_array_t val);
      `CHECK_CHANDLE_VAL(val[0][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(val[1][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(val[2][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(val[3][0][0], get_non_null());
      val[0][0][0] = null;
      val[1][0][0] = null;
      val[2][0][0] = null;
      val[3][0][0] = null;
   endfunction


   function void e_string_0d(inout string val);
      `CHECK_STRING_VAL(val, "42");
      val = "43";
   endfunction
   function void e_string_1d(inout string val[2]);
      `CHECK_STRING_VAL(val[0], "43");
      `CHECK_STRING_VAL(val[1], "44");
      val[0] = "44";
      val[1] = "45";
   endfunction
   function void e_string_2d(inout string val[3][2]);
      `CHECK_STRING_VAL(val[0][1], "45");
      `CHECK_STRING_VAL(val[1][1], "46");
      `CHECK_STRING_VAL(val[2][1], "47");
      val[0][1] = "46";
      val[1][1] = "47";
      val[2][1] = "48";
   endfunction
   function void e_string_3d(inout string_array_t val);
      `CHECK_STRING_VAL(val[0][0][0], "48");
      `CHECK_STRING_VAL(val[1][0][0], "49");
      `CHECK_STRING_VAL(val[2][0][0], "50");
      `CHECK_STRING_VAL(val[3][0][0], "51");
      val[0][0][0] = "49";
      val[1][0][0] = "50";
      val[2][0][0] = "51";
      val[3][0][0] = "52";
   endfunction

   function void e_bit1_0d(inout bit val); `UPDATE_0D(val); endfunction
   function void e_bit1_1d(inout bit val[2]); `UPDATE_1D(val); endfunction
   function void e_bit1_2d(inout bit val[3][2]); `UPDATE_2D(val); endfunction
   function void e_bit1_3d(inout bit1_array_t val); `UPDATE_3D(val); endfunction

   function void e_bit7_0d(inout bit[6:0] val); `UPDATE_0D(val); endfunction
   function void e_bit7_1d(inout bit[6:0] val[2]); `UPDATE_1D(val); endfunction
   function void e_bit7_2d(inout bit[6:0] val[3][2]); `UPDATE_2D(val); endfunction
   function void e_bit7_3d(inout bit7_array_t val); `UPDATE_3D(val); endfunction

   function void e_bit121_0d(inout bit[120:0] val); `UPDATE_0D(val); endfunction
   function void e_bit121_1d(inout bit[120:0] val[2]); `UPDATE_1D(val); endfunction
   function void e_bit121_2d(inout bit[120:0] val[3][2]); `UPDATE_2D(val); endfunction
   function void e_bit121_3d(inout bit121_array_t val); `UPDATE_3D(val); endfunction

   function void e_logic1_0d(inout logic val); `UPDATE_0D(val); endfunction
   function void e_logic1_1d(inout logic val[2]); `UPDATE_1D(val); endfunction
   function void e_logic1_2d(inout logic val[3][2]); `UPDATE_2D(val); endfunction
   function void e_logic1_3d(inout logic1_array_t val); `UPDATE_3D(val); endfunction

   function void e_logic7_0d(inout logic[6:0] val); `UPDATE_0D(val); endfunction
   function void e_logic7_1d(inout logic[6:0] val[2]); `UPDATE_1D(val); endfunction
   function void e_logic7_2d(inout logic[6:0] val[3][2]); `UPDATE_2D(val); endfunction
   function void e_logic7_3d(inout logic7_array_t val); `UPDATE_3D(val); endfunction

   function void e_logic121_0d(inout logic[120:0] val); `UPDATE_0D(val); endfunction
   function void e_logic121_1d(inout logic[120:0] val[2]); `UPDATE_1D(val); endfunction
   function void e_logic121_2d(inout logic[120:0] val[3][2]); `UPDATE_2D(val); endfunction
   function void e_logic121_3d(inout logic121_array_t val); `UPDATE_3D(val); endfunction

   function void e_pack_struct_0d(inout pack_struct_t val); `UPDATE_0D(val); endfunction
   function void e_pack_struct_1d(inout pack_struct_t val[2]); `UPDATE_1D(val); endfunction
   function void e_pack_struct_2d(inout pack_struct_t val[3][2]); `UPDATE_2D(val); endfunction
   function void e_pack_struct_3d(inout pack_struct_array_t val); `UPDATE_3D(val); endfunction

`ifndef NO_UNPACK_STRUCT
   function void e_unpack_struct_0d(inout unpack_struct_t val);
      `CHECK_VAL(val.val, 42);
      val.val = 43;
   endfunction
   function void e_unpack_struct_1d(inout unpack_struct_t val[2]);
      `CHECK_VAL(val[0].val, 43);
      `CHECK_VAL(val[1].val, 44);
      val[0].val = 44;
      val[1].val = 45;
   endfunction
   function void e_unpack_struct_2d(inout unpack_struct_t val[3][2]);
      `CHECK_VAL(val[0][1].val, 45);
      `CHECK_VAL(val[1][1].val, 46);
      `CHECK_VAL(val[2][1].val, 47);
      val[0][1].val = 46;
      val[1][1].val = 47;
      val[2][1].val = 48;
   endfunction
   function void e_unpack_struct_3d(inout unpack_struct_array_t val);
      `CHECK_VAL(val[0][0][0].val, 48);
      `CHECK_VAL(val[1][0][0].val, 49);
      `CHECK_VAL(val[2][0][0].val, 50);
      `CHECK_VAL(val[3][0][0].val, 51);
      val[0][0][0].val = 49;
      val[1][0][0].val = 50;
      val[2][0][0].val = 51;
      val[3][0][0].val = 52;
   endfunction
`endif

   //======================================================================
   // Invoke all imported functions
   //======================================================================

   import "DPI-C" context function void check_exports();
   initial begin
      byte_t byte_array_0d;
      byte_t byte_array_1d[2];
      byte_t byte_array_2d[3][2];
      byte_array_t byte_array;
      byte_unsigned_t byte_unsigned_array_0d;
      byte_unsigned_t byte_unsigned_array_1d[2];
      byte_unsigned_t byte_unsigned_array_2d[3][2];
      byte_unsigned_array_t byte_unsigned_array;
      shortint_t shortint_array_0d;
      shortint_t shortint_array_1d[2];
      shortint_t shortint_array_2d[3][2];
      shortint_array_t shortint_array;
      shortint_unsigned_t shortint_unsigned_array_0d;
      shortint_unsigned_t shortint_unsigned_array_1d[2];
      shortint_unsigned_t shortint_unsigned_array_2d[3][2];
      shortint_unsigned_array_t shortint_unsigned_array;
      int_t int_array_0d;
      int_t int_array_1d[2];
      int_t int_array_2d[3][2];
      int_array_t int_array;
      int_unsigned_t int_unsigned_array_0d;
      int_unsigned_t int_unsigned_array_1d[2];
      int_unsigned_t int_unsigned_array_2d[3][2];
      int_unsigned_array_t int_unsigned_array;
      longint_t longint_array_0d;
      longint_t longint_array_1d[2];
      longint_t longint_array_2d[3][2];
      longint_array_t longint_array;
      longint_unsigned_t longint_unsigned_array_0d;
      longint_unsigned_t longint_unsigned_array_1d[2];
      longint_unsigned_t longint_unsigned_array_2d[3][2];
      longint_unsigned_array_t longint_unsigned_array;
`ifndef NO_TIME
      time_t time_array_0d;
      time_t time_array_1d[2];
      time_t time_array_2d[3][2];
      time_array_t time_array;
`endif
`ifndef NO_INTEGER
      integer_t integer_array_0d;
      integer_t integer_array_1d[2];
      integer_t integer_array_2d[3][2];
      integer_array_t integer_array;
`endif
      real_t real_array_0d;
      real_t real_array_1d[2];
      real_t real_array_2d[3][2];
      real_array_t real_array;
`ifndef NO_SHORTREAL
      shortreal_t shortreal_array_0d;
      shortreal_t shortreal_array_1d[2];
      shortreal_t shortreal_array_2d[3][2];
      shortreal_array_t shortreal_array;
`endif
      chandle_t chandle_array_0d;
      chandle_t chandle_array_1d[2];
      chandle_t chandle_array_2d[3][2];
      chandle_array_t chandle_array;

      string_t string_array_0d;
      string_t string_array_1d[2];
      string_t string_array_2d[3][2];
      string_array_t string_array;

      bit1_t bit1_array_0d;
      bit1_t bit1_array_1d[2];
      bit1_t bit1_array_2d[3][2];
      bit1_array_t bit1_array;

      bit7_t bit7_array_0d;
      bit7_t bit7_array_1d[2];
      bit7_t bit7_array_2d[3][2];
      bit7_array_t bit7_array;

      bit121_t bit121_array_0d;
      bit121_t bit121_array_1d[2];
      bit121_t bit121_array_2d[3][2];
      bit121_array_t bit121_array;

      logic1_t logic1_array_0d;
      logic1_t logic1_array_1d[2];
      logic1_t logic1_array_2d[3][2];
      logic1_array_t logic1_array;

      logic7_t logic7_array_0d;
      logic7_t logic7_array_1d[2];
      logic7_t logic7_array_2d[3][2];
      logic7_array_t logic7_array;

      logic121_t logic121_array_0d;
      logic121_t logic121_array_1d[2];
      logic121_t logic121_array_2d[3][2];
      logic121_array_t logic121_array;

      pack_struct_t pack_struct_array_0d;
      pack_struct_t pack_struct_array_1d[2];
      pack_struct_t pack_struct_array_2d[3][2];
      pack_struct_array_t pack_struct_array;

`ifndef NO_UNPACK_STRUCT
      unpack_struct_t unpack_struct_array_0d;
      unpack_struct_t unpack_struct_array_1d[2];
      unpack_struct_t unpack_struct_array_2d[3][2];
      unpack_struct_array_t unpack_struct_array;
`endif

      `SET_VALUES(byte_array);
      `SET_VALUE_0D(byte_array_0d);
      `SET_VALUE_1D(byte_array_1d);
      `SET_VALUE_2D(byte_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_byte_0d(byte_array[3][2][1]);
      `CHECK_0D(byte_array[3][2][1]);
      i_byte_1d(byte_array[2][1]);
      `CHECK_1D(byte_array[2][1]);
      i_byte_2d(byte_array[1]);
      `CHECK_2D(byte_array[1]);
`endif
      i_byte_0d(byte_array_0d);
      `CHECK_0D(byte_array_0d);
      i_byte_1d(byte_array_1d);
      `CHECK_1D(byte_array_1d);
      i_byte_2d(byte_array_2d);
      `CHECK_2D(byte_array_2d);
      i_byte_3d(byte_array);
      `CHECK_3D(byte_array);

      `SET_VALUES(byte_unsigned_array);
      `SET_VALUE_0D(byte_unsigned_array_0d);
      `SET_VALUE_1D(byte_unsigned_array_1d);
      `SET_VALUE_2D(byte_unsigned_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_byte_unsigned_0d(byte_unsigned_array[3][2][1]);
      `CHECK_0D(byte_unsigned_array[3][2][1]);
      i_byte_unsigned_1d(byte_unsigned_array[2][1]);
      `CHECK_1D(byte_unsigned_array[2][1]);
      i_byte_unsigned_2d(byte_unsigned_array[1]);
      `CHECK_2D(byte_unsigned_array[1]);
`endif
      i_byte_unsigned_0d(byte_unsigned_array_0d);
      `CHECK_0D(byte_unsigned_array_0d);
      i_byte_unsigned_1d(byte_unsigned_array_1d);
      `CHECK_1D(byte_unsigned_array_1d);
      i_byte_unsigned_2d(byte_unsigned_array_2d);
      `CHECK_2D(byte_unsigned_array_2d);
      i_byte_unsigned_3d(byte_unsigned_array);
      `CHECK_3D(byte_unsigned_array);

      `SET_VALUES(shortint_array);
      `SET_VALUE_0D(shortint_array_0d);
      `SET_VALUE_1D(shortint_array_1d);
      `SET_VALUE_2D(shortint_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_shortint_0d(shortint_array[3][2][1]);
      `CHECK_0D(shortint_array[3][2][1]);
      i_shortint_1d(shortint_array[2][1]);
      `CHECK_1D(shortint_array[2][1]);
      i_shortint_2d(shortint_array[1]);
      `CHECK_2D(shortint_array[1]);
`endif
      i_shortint_0d(shortint_array_0d);
      `CHECK_0D(shortint_array_0d);
      i_shortint_1d(shortint_array_1d);
      `CHECK_1D(shortint_array_1d);
      i_shortint_2d(shortint_array_2d);
      `CHECK_2D(shortint_array_2d);
      i_shortint_3d(shortint_array);
      `CHECK_3D(shortint_array);

      `SET_VALUES(shortint_unsigned_array);
      `SET_VALUE_0D(shortint_unsigned_array_0d);
      `SET_VALUE_1D(shortint_unsigned_array_1d);
      `SET_VALUE_2D(shortint_unsigned_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_shortint_unsigned_0d(shortint_unsigned_array[3][2][1]);
      `CHECK_0D(shortint_unsigned_array[3][2][1]);
      i_shortint_unsigned_1d(shortint_unsigned_array[2][1]);
      `CHECK_1D(shortint_unsigned_array[2][1]);
      i_shortint_unsigned_2d(shortint_unsigned_array[1]);
      `CHECK_2D(shortint_unsigned_array[1]);
`endif
      i_shortint_unsigned_0d(shortint_unsigned_array_0d);
      `CHECK_0D(shortint_unsigned_array_0d);
      i_shortint_unsigned_1d(shortint_unsigned_array_1d);
      `CHECK_1D(shortint_unsigned_array_1d);
      i_shortint_unsigned_2d(shortint_unsigned_array_2d);
      `CHECK_2D(shortint_unsigned_array_2d);
      i_shortint_unsigned_3d(shortint_unsigned_array);
      `CHECK_3D(shortint_unsigned_array);

      `SET_VALUES(int_array);
      `SET_VALUE_0D(int_array_0d);
      `SET_VALUE_1D(int_array_1d);
      `SET_VALUE_2D(int_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_int_0d(int_array[3][2][1]);
      `CHECK_0D(int_array[3][2][1]);
      i_int_1d(int_array[2][1]);
      `CHECK_1D(int_array[2][1]);
      i_int_2d(int_array[1]);
      `CHECK_2D(int_array[1]);
`endif
      i_int_0d(int_array_0d);
      `CHECK_0D(int_array_0d);
      i_int_1d(int_array_1d);
      `CHECK_1D(int_array_1d);
      i_int_2d(int_array_2d);
      `CHECK_2D(int_array_2d);
      i_int_3d(int_array);
      `CHECK_3D(int_array);

      `SET_VALUES(int_unsigned_array);
      `SET_VALUE_0D(int_unsigned_array_0d);
      `SET_VALUE_1D(int_unsigned_array_1d);
      `SET_VALUE_2D(int_unsigned_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_int_unsigned_0d(int_unsigned_array[3][2][1]);
      `CHECK_0D(int_unsigned_array[3][2][1]);
      i_int_unsigned_1d(int_unsigned_array[2][1]);
      `CHECK_1D(int_unsigned_array[2][1]);
      i_int_unsigned_2d(int_unsigned_array[1]);
      `CHECK_2D(int_unsigned_array[1]);
`endif
      i_int_unsigned_0d(int_unsigned_array_0d);
      `CHECK_0D(int_unsigned_array_0d);
      i_int_unsigned_1d(int_unsigned_array_1d);
      `CHECK_1D(int_unsigned_array_1d);
      i_int_unsigned_2d(int_unsigned_array_2d);
      `CHECK_2D(int_unsigned_array_2d);
      i_int_unsigned_3d(int_unsigned_array);
      `CHECK_3D(int_unsigned_array);

      `SET_VALUES(longint_array);
      `SET_VALUE_0D(longint_array_0d);
      `SET_VALUE_1D(longint_array_1d);
      `SET_VALUE_2D(longint_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_longint_0d(longint_array[3][2][1]);
      `CHECK_0D(longint_array[3][2][1]);
      i_longint_1d(longint_array[2][1]);
      `CHECK_1D(longint_array[2][1]);
      i_longint_2d(longint_array[1]);
      `CHECK_2D(longint_array[1]);
`endif
      i_longint_0d(longint_array_0d);
      `CHECK_0D(longint_array_0d);
      i_longint_1d(longint_array_1d);
      `CHECK_1D(longint_array_1d);
      i_longint_2d(longint_array_2d);
      `CHECK_2D(longint_array_2d);
      i_longint_3d(longint_array);
      `CHECK_3D(longint_array);

      `SET_VALUES(longint_unsigned_array);
      `SET_VALUE_0D(longint_unsigned_array_0d);
      `SET_VALUE_1D(longint_unsigned_array_1d);
      `SET_VALUE_2D(longint_unsigned_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_longint_unsigned_0d(longint_unsigned_array[3][2][1]);
      `CHECK_0D(longint_unsigned_array[3][2][1]);
      i_longint_unsigned_1d(longint_unsigned_array[2][1]);
      `CHECK_1D(longint_unsigned_array[2][1]);
      i_longint_unsigned_2d(longint_unsigned_array[1]);
      `CHECK_2D(longint_unsigned_array[1]);
`endif
      i_longint_unsigned_0d(longint_unsigned_array_0d);
      `CHECK_0D(longint_unsigned_array_0d);
      i_longint_unsigned_1d(longint_unsigned_array_1d);
      `CHECK_1D(longint_unsigned_array_1d);
      i_longint_unsigned_2d(longint_unsigned_array_2d);
      `CHECK_2D(longint_unsigned_array_2d);
      i_longint_unsigned_3d(longint_unsigned_array);
      `CHECK_3D(longint_unsigned_array);

`ifndef NO_TIME
      `SET_VALUES(time_array);
      `SET_VALUE_0D(time_array_0d);
      `SET_VALUE_1D(time_array_1d);
      `SET_VALUE_2D(time_array_2d);
 `ifndef NO_INOUT_COMPLEX_TYPE
      i_time_0d(time_array[3][2][1]);
      `CHECK_0D(time_array[3][2][1]);
      i_time_1d(time_array[2][1]);
      `CHECK_1D(time_array[2][1]);
      i_time_2d(time_array[1]);
      `CHECK_2D(time_array[1]);
 `endif
      i_time_0d(time_array_0d);
      `CHECK_0D(time_array_0d);
      i_time_1d(time_array_1d);
      `CHECK_1D(time_array_1d);
      i_time_2d(time_array_2d);
      `CHECK_2D(time_array_2d);
      i_time_3d(time_array);
      `CHECK_3D(time_array);
`endif

`ifndef NO_INTEGER
      `SET_VALUES(integer_array);
      `SET_VALUE_0D(integer_array_0d);
      `SET_VALUE_1D(integer_array_1d);
      `SET_VALUE_2D(integer_array_2d);
 `ifndef NO_INOUT_COMPLEX_TYPE
      i_integer_0d(integer_array[3][2][1]);
      `CHECK_0D(integer_array[3][2][1]);
      i_integer_1d(integer_array[2][1]);
      `CHECK_1D(integer_array[2][1]);
      i_integer_2d(integer_array[1]);
      `CHECK_2D(integer_array[1]);
 `endif
      i_integer_0d(integer_array_0d);
      `CHECK_0D(integer_array_0d);
      i_integer_1d(integer_array_1d);
      `CHECK_1D(integer_array_1d);
      i_integer_2d(integer_array_2d);
      `CHECK_2D(integer_array_2d);
      i_integer_3d(integer_array);
      `CHECK_3D(integer_array);
`endif

      `SET_VALUES(real_array);
      `SET_VALUE_0D(real_array_0d);
      `SET_VALUE_1D(real_array_1d);
      `SET_VALUE_2D(real_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_real_0d(real_array[3][2][1]);
      `CHECK_DOUBLE_0D(real_array[3][2][1]);
      i_real_1d(real_array[2][1]);
      `CHECK_DOUBLE_1D(real_array[2][1]);
      i_real_2d(real_array[1]);
      `CHECK_DOUBLE_2D(real_array[1]);
`endif
      i_real_0d(real_array_0d);
      `CHECK_DOUBLE_0D(real_array_0d);
      i_real_1d(real_array_1d);
      `CHECK_DOUBLE_1D(real_array_1d);
      i_real_2d(real_array_2d);
      `CHECK_DOUBLE_2D(real_array_2d);
      i_real_3d(real_array);
      `CHECK_DOUBLE_3D(real_array);

`ifndef NO_SHORTREAL
      `SET_VALUES(shortreal_array);
      `SET_VALUE_0D(shortreal_array_0d);
      `SET_VALUE_1D(shortreal_array_1d);
      `SET_VALUE_2D(shortreal_array_2d);
 `ifndef NO_INOUT_COMPLEX_TYPE
      i_shortreal_0d(shortreal_array[3][2][1]);
      `CHECK_DOUBLE_0D(shortreal_array[3][2][1]);
      i_shortreal_1d(shortreal_array[2][1]);
      `CHECK_DOUBLE_1D(shortreal_array[2][1]);
      i_shortreal_2d(shortreal_array[1]);
      `CHECK_DOUBLE_2D(shortreal_array[1]);
 `endif
      i_shortreal_0d(shortreal_array_0d);
      `CHECK_DOUBLE_0D(shortreal_array_0d);
      i_shortreal_1d(shortreal_array_1d);
      `CHECK_DOUBLE_1D(shortreal_array_1d);
      i_shortreal_2d(shortreal_array_2d);
      `CHECK_DOUBLE_2D(shortreal_array_2d);
      i_shortreal_3d(shortreal_array);
      `CHECK_DOUBLE_3D(shortreal_array);
`endif

      for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 3; ++j)
          for (int k = 0; k < 2; ++k)
            chandle_array[i][j][k] = null;
`ifndef NO_INOUT_COMPLEX_TYPE
      i_chandle_0d(chandle_array[3][2][1]);
      `CHECK_CHANDLE_VAL(chandle_array[3][2][1], get_non_null());
      i_chandle_1d(chandle_array[2][1]);
      `CHECK_CHANDLE_VAL(chandle_array[2][1][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[2][1][1], get_non_null());
      i_chandle_2d(chandle_array[1]);
      `CHECK_CHANDLE_VAL(chandle_array[1][0][1], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[1][1][1], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[1][2][1], get_non_null());
`endif
      chandle_array_0d = null;
      i_chandle_0d(chandle_array_0d);
      `CHECK_CHANDLE_VAL(chandle_array_0d, get_non_null());
      chandle_array_1d[0] = null;
      chandle_array_1d[1] = null;
      i_chandle_1d(chandle_array_1d);
      `CHECK_CHANDLE_VAL(chandle_array_1d[0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array_1d[1], get_non_null());
      chandle_array_2d[0][1] = null;
      chandle_array_2d[1][1] = null;
      chandle_array_2d[2][1] = null;
      i_chandle_2d(chandle_array_2d);
      `CHECK_CHANDLE_VAL(chandle_array_2d[0][1], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array_2d[1][1], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array_2d[2][1], get_non_null());
      i_chandle_3d(chandle_array);
      `CHECK_CHANDLE_VAL(chandle_array[0][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[1][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[2][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[3][0][0], get_non_null());

`ifndef NO_INOUT_COMPLEX_TYPE
      string_array[3][2][1] = "42";
      i_string_0d(string_array[3][2][1]);
      `CHECK_STRING_VAL(string_array[3][2][1], "43");

      string_array[2][1][0] = "43";
      string_array[2][1][1] = "44";
      i_string_1d(string_array[2][1]);
      `CHECK_STRING_VAL(string_array[2][1][0], "44");
      `CHECK_STRING_VAL(string_array[2][1][1], "45");

      string_array[1][0][1] = "45";
      string_array[1][1][1] = "46";
      string_array[1][2][1] = "47";
      i_string_2d(string_array[1]);
      `CHECK_STRING_VAL(string_array[1][0][1], "46");
      `CHECK_STRING_VAL(string_array[1][1][1], "47");
      `CHECK_STRING_VAL(string_array[1][2][1], "48");
`endif
      string_array_0d = "42";
      i_string_0d(string_array_0d);
      `CHECK_STRING_VAL(string_array_0d, "43");
      string_array_1d[0] = "43";
      string_array_1d[1] = "44";
      i_string_1d(string_array_1d);
      `CHECK_STRING_VAL(string_array_1d[0], "44");
      `CHECK_STRING_VAL(string_array_1d[1], "45");

      string_array_2d[0][1] = "45";
      string_array_2d[1][1] = "46";
      string_array_2d[2][1] = "47";
      i_string_2d(string_array_2d);
      `CHECK_STRING_VAL(string_array_2d[0][1], "46");
      `CHECK_STRING_VAL(string_array_2d[1][1], "47");
      `CHECK_STRING_VAL(string_array_2d[2][1], "48");

      string_array[0][0][0] = "48";
      string_array[1][0][0] = "49";
      string_array[2][0][0] = "50";
      string_array[3][0][0] = "51";
      i_string_3d(string_array);
      `CHECK_STRING_VAL(string_array[0][0][0], "49");
      `CHECK_STRING_VAL(string_array[1][0][0], "50");
      `CHECK_STRING_VAL(string_array[2][0][0], "51");
      `CHECK_STRING_VAL(string_array[3][0][0], "52");

      `SET_VALUES(bit1_array);
      `SET_VALUE_0D(bit1_array_0d);
      `SET_VALUE_1D(bit1_array_1d);
      `SET_VALUE_2D(bit1_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_bit1_0d(bit1_array[3][2][1]);
      `CHECK_0D(bit1_array[3][2][1]);
      i_bit1_1d(bit1_array[2][1]);
      `CHECK_1D(bit1_array[2][1]);
      i_bit1_2d(bit1_array[1]);
      `CHECK_2D(bit1_array[1]);
`endif
      i_bit1_0d(bit1_array_0d);
      `CHECK_0D(bit1_array_0d);
      i_bit1_1d(bit1_array_1d);
      `CHECK_1D(bit1_array_1d);
      i_bit1_2d(bit1_array_2d);
      `CHECK_2D(bit1_array_2d);
      i_bit1_3d(bit1_array);
      `CHECK_3D(bit1_array);

      `SET_VALUES(bit7_array);
      `SET_VALUE_0D(bit7_array_0d);
      `SET_VALUE_1D(bit7_array_1d);
      `SET_VALUE_2D(bit7_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_bit7_0d(bit7_array[3][2][1]);
      `CHECK_0D(bit7_array[3][2][1]);
      i_bit7_1d(bit7_array[2][1]);
      `CHECK_1D(bit7_array[2][1]);
      i_bit7_2d(bit7_array[1]);
      `CHECK_2D(bit7_array[1]);
`endif
      i_bit7_0d(bit7_array_0d);
      `CHECK_0D(bit7_array_0d);
      i_bit7_1d(bit7_array_1d);
      `CHECK_1D(bit7_array_1d);
      i_bit7_2d(bit7_array_2d);
      `CHECK_2D(bit7_array_2d);
      i_bit7_3d(bit7_array);
      `CHECK_3D(bit7_array);

      `SET_VALUES(bit121_array);
      `SET_VALUE_0D(bit121_array_0d);
      `SET_VALUE_1D(bit121_array_1d);
      `SET_VALUE_2D(bit121_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_bit121_0d(bit121_array[3][2][1]);
      `CHECK_0D(bit121_array[3][2][1]);
      i_bit121_1d(bit121_array[2][1]);
      `CHECK_1D(bit121_array[2][1]);
      i_bit121_2d(bit121_array[1]);
      `CHECK_2D(bit121_array[1]);
`endif
      i_bit121_0d(bit121_array_0d);
      `CHECK_0D(bit121_array_0d);
      i_bit121_1d(bit121_array_1d);
      `CHECK_1D(bit121_array_1d);
      i_bit121_2d(bit121_array_2d);
      `CHECK_2D(bit121_array_2d);
      i_bit121_3d(bit121_array);
      `CHECK_3D(bit121_array);

      `SET_VALUES(logic1_array);
      `SET_VALUE_0D(logic1_array_0d);
      `SET_VALUE_1D(logic1_array_1d);
      `SET_VALUE_2D(logic1_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_logic1_0d(logic1_array[3][2][1]);
      `CHECK_0D(logic1_array[3][2][1]);
      i_logic1_1d(logic1_array[2][1]);
      `CHECK_1D(logic1_array[2][1]);
      i_logic1_2d(logic1_array[1]);
      `CHECK_2D(logic1_array[1]);
`endif
      i_logic1_0d(logic1_array_0d);
      `CHECK_0D(logic1_array_0d);
      i_logic1_1d(logic1_array_1d);
      `CHECK_1D(logic1_array_1d);
      i_logic1_2d(logic1_array_2d);
      `CHECK_2D(logic1_array_2d);
      i_logic1_3d(logic1_array);
      `CHECK_3D(logic1_array);

      `SET_VALUES(logic7_array);
      `SET_VALUE_0D(logic7_array_0d);
      `SET_VALUE_1D(logic7_array_1d);
      `SET_VALUE_2D(logic7_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_logic7_0d(logic7_array[3][2][1]);
      `CHECK_0D(logic7_array[3][2][1]);
      i_logic7_1d(logic7_array[2][1]);
      `CHECK_1D(logic7_array[2][1]);
      i_logic7_2d(logic7_array[1]);
      `CHECK_2D(logic7_array[1]);
`endif
      i_logic7_0d(logic7_array_0d);
      `CHECK_0D(logic7_array_0d);
      i_logic7_1d(logic7_array_1d);
      `CHECK_1D(logic7_array_1d);
      i_logic7_2d(logic7_array_2d);
      `CHECK_2D(logic7_array_2d);
      i_logic7_3d(logic7_array);
      `CHECK_3D(logic7_array);

      `SET_VALUES(logic121_array);
      `SET_VALUE_0D(logic121_array_0d);
      `SET_VALUE_1D(logic121_array_1d);
      `SET_VALUE_2D(logic121_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_logic121_0d(logic121_array[3][2][1]);
      `CHECK_0D(logic121_array[3][2][1]);
      i_logic121_1d(logic121_array[2][1]);
      `CHECK_1D(logic121_array[2][1]);
      i_logic121_2d(logic121_array[1]);
      `CHECK_2D(logic121_array[1]);
`endif
      i_logic121_0d(logic121_array_0d);
      `CHECK_0D(logic121_array_0d);
      i_logic121_1d(logic121_array_1d);
      `CHECK_1D(logic121_array_1d);
      i_logic121_2d(logic121_array_2d);
      `CHECK_2D(logic121_array_2d);
      i_logic121_3d(logic121_array);
      `CHECK_3D(logic121_array);

      `SET_VALUES(pack_struct_array);
      `SET_VALUE_0D(pack_struct_array_0d);
      `SET_VALUE_1D(pack_struct_array_1d);
      `SET_VALUE_2D(pack_struct_array_2d);
`ifndef NO_INOUT_COMPLEX_TYPE
      i_pack_struct_0d(pack_struct_array[3][2][1]);
      `CHECK_0D(pack_struct_array[3][2][1]);
      i_pack_struct_1d(pack_struct_array[2][1]);
      `CHECK_1D(pack_struct_array[2][1]);
      i_pack_struct_2d(pack_struct_array[1]);
      `CHECK_2D(pack_struct_array[1]);
`endif
      i_pack_struct_0d(pack_struct_array_0d);
      `CHECK_0D(pack_struct_array_0d);
      i_pack_struct_1d(pack_struct_array_1d);
      `CHECK_1D(pack_struct_array_1d);
      i_pack_struct_2d(pack_struct_array_2d);
      `CHECK_2D(pack_struct_array_2d);
      i_pack_struct_3d(pack_struct_array);
      `CHECK_3D(pack_struct_array);

`ifndef NO_UNPACK_STRUCT
      unpack_struct_array[3][2][1].val = 42;
      i_unpack_struct_0d(unpack_struct_array[3][2][1]);
      `CHECK_VAL(unpack_struct_array[3][2][1].val, 43);

      unpack_struct_array[2][1][0].val = 43;
      unpack_struct_array[2][1][1].val = 44;
      i_unpack_struct_1d(unpack_struct_array[2][1]);
      `CHECK_VAL(unpack_struct_array[2][1][0].val, 44);
      `CHECK_VAL(unpack_struct_array[2][1][1].val, 45);

      unpack_struct_array[1][0][1].val = 45;
      unpack_struct_array[1][1][1].val = 46;
      unpack_struct_array[1][2][1].val = 47;
      i_unpack_struct_2d(unpack_struct_array[1]);
      `CHECK_VAL(unpack_struct_array[1][0][1].val, 46);
      `CHECK_VAL(unpack_struct_array[1][1][1].val, 47);
      `CHECK_VAL(unpack_struct_array[1][2][1].val, 48);

      unpack_struct_array[0][0][0].val = 48;
      unpack_struct_array[1][0][0].val = 49;
      unpack_struct_array[2][0][0].val = 50;
      unpack_struct_array[3][0][0].val = 51;
      i_unpack_struct_3d(unpack_struct_array);
      `CHECK_VAL(unpack_struct_array[0][0][0].val, 49);
      `CHECK_VAL(unpack_struct_array[1][0][0].val, 50);
      `CHECK_VAL(unpack_struct_array[2][0][0].val, 51);
      `CHECK_VAL(unpack_struct_array[3][0][0].val, 52);
`endif

      check_exports();
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
