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
`endif

`ifdef NO_BITS_TO_SCALAR
 `define ARE_SAME(act, exp) ($bits((act)) == 1 ? (act) == ((exp) & 1) : (act) == (exp))
`else
 `define ARE_SAME(act, exp) ((act) == (($bits(act))'(exp)))
`endif

`define CHECK_VAL(act, exp) if (`ARE_SAME(act, exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":", (act), " as expected"); \
     end else begin \
        $display("Mismatch %s expected:%d actual:%d at %d", `"act`", \
                 int'(exp), \
                 int'(act), `__LINE__); \
          $stop; \
            end

`define CHECK_0D(val) `CHECK_VAL((val), 42)
`define CHECK_1D(val) `CHECK_VAL(val[0], 43); \
`CHECK_VAL(val[1], 44)
`define CHECK_2D(val) `CHECK_VAL(val[0][1], 45); \
`CHECK_VAL(val[1][1], 46); \
`CHECK_VAL(val[2][1], 47)
`define CHECK_3D(val) `CHECK_VAL(val[0][0][0], 48); \
`CHECK_VAL(val[1][0][0], 49); \
`CHECK_VAL(val[2][0][0], 50); \
`CHECK_VAL(val[3][0][0], 51)

`define CHECK_CHANDLE_VAL(act, exp) if ((act) == (exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":non-null as expected"); \
     end else begin \
        $display("Mismatch %s expected:%s but %s at %d", `"act`", \
                 (exp) ? "null" : "non-null", (act) ? "null" : "non-null", `__LINE__); \
          $stop; \
            end

`define CHECK_STRING_VAL(act, exp) if ((act) == (exp)) begin \
   if (ENABLE_VERBOSE_MESSAGE)$display(`"act`", ":", (act), " as expected"); \
     end else begin \
        $display("Mismatch %s expected:%s actual:%s at %d", \
                 `"act`", (exp), (act), `__LINE__); \
          $stop; \
            end

`define SET_VALUES(val) \
val[3][2][1] = 42; \
val[2][1][0] = 43; val[2][1][1] = 44; \
val[1][0][1] = 45; val[1][1][1] = 46; val[1][2][1] = 47; \
val[0][0][0] = 48; val[1][0][0] = 49; val[2][0][0] = 50; val[3][0][0] = 51

module t;

   localparam ENABLE_VERBOSE_MESSAGE = 0;

   // Legal output argument types for DPI functions

   //======================================================================
   // Type definitions
   //======================================================================

   typedef byte byte_array_t[4][3][2];
   typedef byte unsigned byte_unsigned_array_t[4][3][2];
   typedef shortint      shortint_array_t[4][3][2];
   typedef shortint unsigned shortint_unsigned_array_t[4][3][2];
   typedef int               int_array_t[4][3][2];
   typedef int unsigned      int_unsigned_array_t[4][3][2];
   typedef longint           longint_array_t[4][3][2];
   typedef longint unsigned  longint_unsigned_array_t[4][3][2];
`ifndef NO_TIME
   typedef time              time_array_t[4][3][2];
`endif
`ifndef NO_INTEGER
   typedef integer           integer_array_t[4][3][2];
`endif
   typedef real              real_array_t[4][3][2];
`ifndef NO_SHORTREAL
   typedef shortreal         shortreal_array_t[4][3][2];
`endif
   typedef chandle           chandle_array_t[4][3][2];
   typedef string            string_array_t[4][3][2];
   typedef bit               bit1_array_t[4][3][2];
   typedef bit [6:0]         bit7_array_t[4][3][2];
   typedef bit [120:0]       bit121_array_t[4][3][2];
   typedef logic             logic1_array_t[4][3][2];
   typedef logic [6:0]       logic7_array_t[4][3][2];
   typedef logic [120:0]     logic121_array_t[4][3][2];

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

   import "DPI-C" function void i_byte_0d(output byte val);
   import "DPI-C" function void i_byte_1d(output byte val[2]);
   import "DPI-C" function void i_byte_2d(output byte val[3][2]);
   import "DPI-C" function void i_byte_3d(output byte_array_t val);

   import "DPI-C" function void i_byte_unsigned_0d(output byte unsigned val);
   import "DPI-C" function void i_byte_unsigned_1d(output byte unsigned val[2]);
   import "DPI-C" function void i_byte_unsigned_2d(output byte unsigned val[3][2]);
   import "DPI-C" function void i_byte_unsigned_3d(output byte_unsigned_array_t val);

   import "DPI-C" function void i_shortint_0d(output shortint val);
   import "DPI-C" function void i_shortint_1d(output shortint val[2]);
   import "DPI-C" function void i_shortint_2d(output shortint val[3][2]);
   import "DPI-C" function void i_shortint_3d(output shortint_array_t val);

   import "DPI-C" function void i_shortint_unsigned_0d(output shortint unsigned val);
   import "DPI-C" function void i_shortint_unsigned_1d(output shortint unsigned val[2]);
   import "DPI-C" function void i_shortint_unsigned_2d(output shortint unsigned val[3][2]);
   import "DPI-C" function void i_shortint_unsigned_3d(output shortint_unsigned_array_t val);

   import "DPI-C" function void i_int_0d(output int val);
   import "DPI-C" function void i_int_1d(output int val[2]);
   import "DPI-C" function void i_int_2d(output int val[3][2]);
   import "DPI-C" function void i_int_3d(output int_array_t val);

   import "DPI-C" function void i_int_unsigned_0d(output int unsigned val);
   import "DPI-C" function void i_int_unsigned_1d(output int unsigned val[2]);
   import "DPI-C" function void i_int_unsigned_2d(output int unsigned val[3][2]);
   import "DPI-C" function void i_int_unsigned_3d(output int_unsigned_array_t val);

   import "DPI-C" function void i_longint_0d(output longint val);
   import "DPI-C" function void i_longint_1d(output longint val[2]);
   import "DPI-C" function void i_longint_2d(output longint val[3][2]);
   import "DPI-C" function void i_longint_3d(output longint_array_t val);

   import "DPI-C" function void i_longint_unsigned_0d(output longint unsigned val);
   import "DPI-C" function void i_longint_unsigned_1d(output longint unsigned val[2]);
   import "DPI-C" function void i_longint_unsigned_2d(output longint unsigned val[3][2]);
   import "DPI-C" function void i_longint_unsigned_3d(output longint_unsigned_array_t val);

`ifndef NO_TIME
   import "DPI-C" function void i_time_0d(output time val);
   import "DPI-C" function void i_time_1d(output time val[2]);
   import "DPI-C" function void i_time_2d(output time val[3][2]);
   import "DPI-C" function void i_time_3d(output time_array_t val);
`endif

`ifndef NO_INTEGER
   import "DPI-C" function void i_integer_0d(output integer val);
   import "DPI-C" function void i_integer_1d(output integer val[2]);
   import "DPI-C" function void i_integer_2d(output integer val[3][2]);
   import "DPI-C" function void i_integer_3d(output integer_array_t val);
`endif

   import "DPI-C" function void i_real_0d(output real val);
   import "DPI-C" function void i_real_1d(output real val[2]);
   import "DPI-C" function void i_real_2d(output real val[3][2]);
   import "DPI-C" function void i_real_3d(output real_array_t val);

`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal_0d(output shortreal val);
   import "DPI-C" function void i_shortreal_1d(output shortreal val[2]);
   import "DPI-C" function void i_shortreal_2d(output shortreal val[3][2]);
   import "DPI-C" function void i_shortreal_3d(output shortreal_array_t val);
`endif

   import "DPI-C" function void i_chandle_0d(output chandle val);
   import "DPI-C" function void i_chandle_1d(output chandle val[2]);
   import "DPI-C" function void i_chandle_2d(output chandle val[3][2]);
   import "DPI-C" function void i_chandle_3d(output chandle_array_t val);

   import "DPI-C" function void i_string_0d(output string val);
   import "DPI-C" function void i_string_1d(output string val[2]);
   import "DPI-C" function void i_string_2d(output string val[3][2]);
   import "DPI-C" function void i_string_3d(output string_array_t val);

   import "DPI-C" function void i_bit1_0d(output bit val);
   import "DPI-C" function void i_bit1_1d(output bit val[2]);
   import "DPI-C" function void i_bit1_2d(output bit val[3][2]);
   import "DPI-C" function void i_bit1_3d(output bit1_array_t val);

   import "DPI-C" function void i_bit7_0d(output bit[6:0] val);
   import "DPI-C" function void i_bit7_1d(output bit[6:0] val[2]);
   import "DPI-C" function void i_bit7_2d(output bit[6:0] val[3][2]);
   import "DPI-C" function void i_bit7_3d(output bit7_array_t val);

   import "DPI-C" function void i_bit121_0d(output bit[120:0] val);
   import "DPI-C" function void i_bit121_1d(output bit[120:0] val[2]);
   import "DPI-C" function void i_bit121_2d(output bit[120:0] val[3][2]);
   import "DPI-C" function void i_bit121_3d(output bit121_array_t val);

   import "DPI-C" function void i_logic1_0d(output logic val);
   import "DPI-C" function void i_logic1_1d(output logic val[2]);
   import "DPI-C" function void i_logic1_2d(output logic val[3][2]);
   import "DPI-C" function void i_logic1_3d(output logic1_array_t val);

   import "DPI-C" function void i_logic7_0d(output logic[6:0] val);
   import "DPI-C" function void i_logic7_1d(output logic[6:0] val[2]);
   import "DPI-C" function void i_logic7_2d(output logic[6:0] val[3][2]);
   import "DPI-C" function void i_logic7_3d(output logic7_array_t val);

   import "DPI-C" function void i_logic121_0d(output logic[120:0] val);
   import "DPI-C" function void i_logic121_1d(output logic[120:0] val[2]);
   import "DPI-C" function void i_logic121_2d(output logic[120:0] val[3][2]);
   import "DPI-C" function void i_logic121_3d(output logic121_array_t val);

   import "DPI-C" function void i_pack_struct_0d(output pack_struct_t val);
   import "DPI-C" function void i_pack_struct_1d(output pack_struct_t val[2]);
   import "DPI-C" function void i_pack_struct_2d(output pack_struct_t val[3][2]);
   import "DPI-C" function void i_pack_struct_3d(output pack_struct_array_t val);

`ifndef NO_UNPACK_STRUCT
   import "DPI-C" function void i_unpack_struct_0d(output unpack_struct_t val);
   import "DPI-C" function void i_unpack_struct_1d(output unpack_struct_t val[2]);
   import "DPI-C" function void i_unpack_struct_2d(output unpack_struct_t val[3][2]);
   import "DPI-C" function void i_unpack_struct_3d(output unpack_struct_array_t val);
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
`define SET_0D(val) \
   /* verilator lint_off WIDTH */ \
   val = 42 \
   /* verilator lint_on WIDTH */
`define SET_1D(val) \
   /* verilator lint_off WIDTH */ \
   val[0] = 43; val[1] = 44 \
   /* verilator lint_on WIDTH */
`define SET_2D(val) \
   /* verilator lint_off WIDTH */ \
   val[0][1] = 45; val[1][1] = 46; val[2][1] = 47 \
   /* verilator lint_on WIDTH */
`define SET_3D(val) \
   /* verilator lint_off WIDTH */ \
   val[0][0][0] = 48; val[1][0][0] = 49; val[2][0][0] = 50; val[3][0][0] = 51 \
   /* verilator lint_on WIDTH */

   function void e_byte_0d(output byte val); `SET_0D(val); endfunction
   function void e_byte_1d(output byte val[2]); `SET_1D(val); endfunction
   function void e_byte_2d(output byte val[3][2]); `SET_2D(val); endfunction
   function void e_byte_3d(output byte_array_t val); `SET_3D(val); endfunction

   function void e_byte_unsigned_0d(output byte unsigned val); `SET_0D(val); endfunction
   function void e_byte_unsigned_1d(output byte unsigned val[2]); `SET_1D(val); endfunction
   function void e_byte_unsigned_2d(output byte unsigned val[3][2]); `SET_2D(val); endfunction
   function void e_byte_unsigned_3d(output byte_unsigned_array_t val); `SET_3D(val); endfunction

   function void e_shortint_0d(output shortint val); `SET_0D(val); endfunction
   function void e_shortint_1d(output shortint val[2]); `SET_1D(val); endfunction
   function void e_shortint_2d(output shortint val[3][2]); `SET_2D(val); endfunction
   function void e_shortint_3d(output shortint_array_t val); `SET_3D(val); endfunction

   function void e_shortint_unsigned_0d(output shortint unsigned val); `SET_0D(val); endfunction
   function void e_shortint_unsigned_1d(output shortint unsigned val[2]); `SET_1D(val); endfunction
   function void e_shortint_unsigned_2d(output shortint unsigned val[3][2]); `SET_2D(val); endfunction
   function void e_shortint_unsigned_3d(output shortint_unsigned_array_t val); `SET_3D(val); endfunction

   function void e_int_0d(output int val); `SET_0D(val); endfunction
   function void e_int_1d(output int val[2]); `SET_1D(val); endfunction
   function void e_int_2d(output int val[3][2]); `SET_2D(val); endfunction
   function void e_int_3d(output int_array_t val); `SET_3D(val); endfunction

   function void e_int_unsigned_0d(output int unsigned val); `SET_0D(val); endfunction
   function void e_int_unsigned_1d(output int unsigned val[2]); `SET_1D(val); endfunction
   function void e_int_unsigned_2d(output int unsigned val[3][2]); `SET_2D(val); endfunction
   function void e_int_unsigned_3d(output int_unsigned_array_t val); `SET_3D(val); endfunction

   function void e_longint_0d(output longint val); `SET_0D(val); endfunction
   function void e_longint_1d(output longint val[2]); `SET_1D(val); endfunction
   function void e_longint_2d(output longint val[3][2]); `SET_2D(val); endfunction
   function void e_longint_3d(output longint_array_t val); `SET_3D(val); endfunction

   function void e_longint_unsigned_0d(output longint unsigned val); `SET_0D(val); endfunction
   function void e_longint_unsigned_1d(output longint unsigned val[2]); `SET_1D(val); endfunction
   function void e_longint_unsigned_2d(output longint unsigned val[3][2]); `SET_2D(val); endfunction
   function void e_longint_unsigned_3d(output longint_unsigned_array_t val); `SET_3D(val); endfunction

`ifndef NO_TIME
   function void e_time_0d(output time val); `SET_0D(val); endfunction
   function void e_time_1d(output time val[2]); `SET_1D(val); endfunction
   function void e_time_2d(output time val[3][2]); `SET_2D(val); endfunction
   function void e_time_3d(output time_array_t val); `SET_3D(val); endfunction
`endif

`ifndef NO_INTEGER
   function void e_integer_0d(output integer val); `SET_0D(val); endfunction
   function void e_integer_1d(output integer val[2]); `SET_1D(val); endfunction
   function void e_integer_2d(output integer val[3][2]); `SET_2D(val); endfunction
   function void e_integer_3d(output integer_array_t val); `SET_3D(val); endfunction
`endif

   function void e_real_0d(output real val); `SET_0D(val); endfunction
   function void e_real_1d(output real val[2]); `SET_1D(val); endfunction
   function void e_real_2d(output real val[3][2]); `SET_2D(val); endfunction
   function void e_real_3d(output real_array_t val); `SET_3D(val); endfunction

`ifndef NO_SHORTREAL
   function void e_shortreal_0d(output shortreal val); `SET_0D(val); endfunction
   function void e_shortreal_1d(output shortreal val[2]); `SET_1D(val); endfunction
   function void e_shortreal_2d(output shortreal val[3][2]); `SET_2D(val); endfunction
   function void e_shortreal_3d(output shortreal_array_t val); `SET_3D(val); endfunction
`endif

   function void e_chandle_0d(output chandle val);
      val = get_non_null();
   endfunction
   function void e_chandle_1d(output chandle val[2]);
      val[0] = get_non_null();
      val[1] = get_non_null();
   endfunction
   function void e_chandle_2d(output chandle val[3][2]);
      val[0][1] = get_non_null();
      val[1][1] = get_non_null();
      val[2][1] = get_non_null();
   endfunction
   function void e_chandle_3d(output chandle_array_t val);
      val[0][0][0] = get_non_null();
      val[1][0][0] = get_non_null();
      val[2][0][0] = get_non_null();
      val[3][0][0] = get_non_null();
   endfunction

   function void e_string_0d(output string val);
      val = "42";
   endfunction
   function void e_string_1d(output string val[2]);
      val[0] = "43";
      val[1] = "44";
   endfunction
   function void e_string_2d(output string val[3][2]);
      val[0][1] = "45";
      val[1][1] = "46";
      val[2][1] = "47";
   endfunction
   function void e_string_3d(output string_array_t val);
      val[0][0][0] = "48";
      val[1][0][0] = "49";
      val[2][0][0] = "50";
      val[3][0][0] = "51";
   endfunction

   function void e_bit1_0d(output bit val); `SET_0D(val); endfunction
   function void e_bit1_1d(output bit val[2]); `SET_1D(val); endfunction
   function void e_bit1_2d(output bit val[3][2]); `SET_2D(val); endfunction
   function void e_bit1_3d(output bit7_array_t val); `SET_3D(val); endfunction

   function void e_bit7_0d(output bit[6:0] val); `SET_0D(val); endfunction
   function void e_bit7_1d(output bit[6:0] val[2]); `SET_1D(val); endfunction
   function void e_bit7_2d(output bit[6:0] val[3][2]); `SET_2D(val); endfunction
   function void e_bit7_3d(output bit7_array_t val); `SET_3D(val); endfunction

   function void e_bit121_0d(output bit[120:0] val); `SET_0D(val); endfunction
   function void e_bit121_1d(output bit[120:0] val[2]); `SET_1D(val); endfunction
   function void e_bit121_2d(output bit[120:0] val[3][2]); `SET_2D(val); endfunction
   function void e_bit121_3d(output bit121_array_t val); `SET_3D(val); endfunction

   function void e_logic1_0d(output logic val); `SET_0D(val); endfunction
   function void e_logic1_1d(output logic val[2]); `SET_1D(val); endfunction
   function void e_logic1_2d(output logic val[3][2]); `SET_2D(val); endfunction
   function void e_logic1_3d(output logic7_array_t val); `SET_3D(val); endfunction

   function void e_logic7_0d(output logic[6:0] val); `SET_0D(val); endfunction
   function void e_logic7_1d(output logic[6:0] val[2]); `SET_1D(val); endfunction
   function void e_logic7_2d(output logic[6:0] val[3][2]); `SET_2D(val); endfunction
   function void e_logic7_3d(output logic7_array_t val); `SET_3D(val); endfunction

   function void e_logic121_0d(output logic[120:0] val); `SET_0D(val); endfunction
   function void e_logic121_1d(output logic[120:0] val[2]); `SET_1D(val); endfunction
   function void e_logic121_2d(output logic[120:0] val[3][2]); `SET_2D(val); endfunction
   function void e_logic121_3d(output logic121_array_t val); `SET_3D(val); endfunction

   function void e_pack_struct_0d(output pack_struct_t val); `SET_0D(val); endfunction
   function void e_pack_struct_1d(output pack_struct_t val[2]); `SET_1D(val); endfunction
   function void e_pack_struct_2d(output pack_struct_t val[3][2]); `SET_2D(val); endfunction
   function void e_pack_struct_3d(output pack_struct_array_t val); `SET_3D(val); endfunction

`ifndef NO_UNPACK_STRUCT
   function void e_unpack_struct_0d(output unpack_struct_t val);
      val.val = 42;
   endfunction
   function void e_unpack_struct_1d(output unpack_struct_t val[2]);
      val[0].val = 43;
      val[1].val = 44;
   endfunction
   function void e_unpack_struct_2d(output unpack_struct_t val[3][2]);
      val[0][1].val = 45;
      val[1][1].val = 46;
      val[2][1].val = 47;
   endfunction
   function void e_unpack_struct_3d(output unpack_struct_array_t val);
      val[0][0][0].val = 48;
      val[1][0][0].val = 49;
      val[2][0][0].val = 50;
      val[3][0][0].val = 51;
   endfunction
`endif

   //======================================================================
   // Invoke all imported functions
   //======================================================================

   import "DPI-C" context function void check_exports();

   initial begin
      byte_array_t byte_array;
      byte_unsigned_array_t byte_unsigned_array;
      shortint_array_t shortint_array;
      shortint_unsigned_array_t shortint_unsigned_array;
      int_array_t int_array;
      int_unsigned_array_t int_unsigned_array;
      longint_array_t longint_array;
      longint_unsigned_array_t longint_unsigned_array;
`ifndef NO_TIME
      time_array_t time_array;
`endif
`ifndef NO_INTEGER
      integer_array_t integer_array;
`endif
      real_array_t real_array;
`ifndef NO_SHORTREAL
      shortreal_array_t shortreal_array;
`endif
      chandle_array_t chandle_array;
      string_array_t string_array;
      bit1_array_t bit1_array;
      bit7_array_t bit7_array;
      bit121_array_t bit121_array;
      logic1_array_t logic1_array;
      logic7_array_t logic7_array;
      logic121_array_t logic121_array;
      pack_struct_array_t pack_struct_array;
`ifndef NO_UNPACK_STRUCT
      unpack_struct_array_t unpack_struct_array;
`endif

      i_byte_0d(byte_array[3][2][1]);
      `CHECK_0D(byte_array[3][2][1]);
      i_byte_1d(byte_array[2][1]);
      `CHECK_1D(byte_array[2][1]);
      i_byte_2d(byte_array[1]);
      `CHECK_2D(byte_array[1]);
      i_byte_3d(byte_array);
      `CHECK_3D(byte_array);

      i_byte_unsigned_0d(byte_unsigned_array[3][2][1]);
      `CHECK_0D(byte_unsigned_array[3][2][1]);
      i_byte_unsigned_1d(byte_unsigned_array[2][1]);
      `CHECK_1D(byte_unsigned_array[2][1]);
      i_byte_unsigned_2d(byte_unsigned_array[1]);
      `CHECK_2D(byte_unsigned_array[1]);
      i_byte_unsigned_3d(byte_unsigned_array);
      `CHECK_3D(byte_unsigned_array);

      i_shortint_0d(shortint_array[3][2][1]);
      `CHECK_0D(shortint_array[3][2][1]);
      i_shortint_1d(shortint_array[2][1]);
      `CHECK_1D(shortint_array[2][1]);
      i_shortint_2d(shortint_array[1]);
      `CHECK_2D(shortint_array[1]);
      i_shortint_3d(shortint_array);
      `CHECK_3D(shortint_array);

      i_shortint_unsigned_0d(shortint_unsigned_array[3][2][1]);
      `CHECK_0D(shortint_unsigned_array[3][2][1]);
      i_shortint_unsigned_1d(shortint_unsigned_array[2][1]);
      `CHECK_1D(shortint_unsigned_array[2][1]);
      i_shortint_unsigned_2d(shortint_unsigned_array[1]);
      `CHECK_2D(shortint_unsigned_array[1]);
      i_shortint_unsigned_3d(shortint_unsigned_array);
      `CHECK_3D(shortint_unsigned_array);

      i_int_0d(int_array[3][2][1]);
      `CHECK_0D(int_array[3][2][1]);
      i_int_1d(int_array[2][1]);
      `CHECK_1D(int_array[2][1]);
      i_int_2d(int_array[1]);
      `CHECK_2D(int_array[1]);
      i_int_3d(int_array);
      `CHECK_3D(int_array);

      i_int_unsigned_0d(int_unsigned_array[3][2][1]);
      `CHECK_0D(int_unsigned_array[3][2][1]);
      i_int_unsigned_1d(int_unsigned_array[2][1]);
      `CHECK_1D(int_unsigned_array[2][1]);
      i_int_unsigned_2d(int_unsigned_array[1]);
      `CHECK_2D(int_unsigned_array[1]);
      i_int_unsigned_3d(int_unsigned_array);
      `CHECK_3D(int_unsigned_array);

      i_longint_0d(longint_array[3][2][1]);
      `CHECK_0D(longint_array[3][2][1]);
      i_longint_1d(longint_array[2][1]);
      `CHECK_1D(longint_array[2][1]);
      i_longint_2d(longint_array[1]);
      `CHECK_2D(longint_array[1]);
      i_longint_3d(longint_array);
      `CHECK_3D(longint_array);

      i_longint_unsigned_0d(longint_unsigned_array[3][2][1]);
      `CHECK_0D(longint_unsigned_array[3][2][1]);
      i_longint_unsigned_1d(longint_unsigned_array[2][1]);
      `CHECK_1D(longint_unsigned_array[2][1]);
      i_longint_unsigned_2d(longint_unsigned_array[1]);
      `CHECK_2D(longint_unsigned_array[1]);
      i_longint_unsigned_3d(longint_unsigned_array);
      `CHECK_3D(longint_unsigned_array);

`ifndef NO_TIME
      i_time_0d(time_array[3][2][1]);
      `CHECK_0D(time_array[3][2][1]);
      i_time_1d(time_array[2][1]);
      `CHECK_1D(time_array[2][1]);
      i_time_2d(time_array[1]);
      `CHECK_2D(time_array[1]);
      i_time_3d(time_array);
      `CHECK_3D(time_array);
`endif

`ifndef NO_INTEGER
      i_integer_0d(integer_array[3][2][1]);
      `CHECK_0D(integer_array[3][2][1]);
      i_integer_1d(integer_array[2][1]);
      `CHECK_1D(integer_array[2][1]);
      i_integer_2d(integer_array[1]);
      `CHECK_2D(integer_array[1]);
      i_integer_3d(integer_array);
      `CHECK_3D(integer_array);
`endif

      i_real_0d(real_array[3][2][1]);
      `CHECK_0D(real_array[3][2][1]);
      i_real_1d(real_array[2][1]);
      `CHECK_1D(real_array[2][1]);
      i_real_2d(real_array[1]);
      `CHECK_2D(real_array[1]);
      i_real_3d(real_array);
      `CHECK_3D(real_array);

`ifndef NO_SHORTREAL
      i_shortreal_0d(shortreal_array[3][2][1]);
      `CHECK_0D(shortreal_array[3][2][1]);
      i_shortreal_1d(shortreal_array[2][1]);
      `CHECK_1D(shortreal_array[2][1]);
      i_shortreal_2d(shortreal_array[1]);
      `CHECK_2D(shortreal_array[1]);
      i_shortreal_3d(shortreal_array);
      `CHECK_3D(shortreal_array);
`endif

      for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 3; ++j)
          for (int k = 0; k < 2; ++k)
            chandle_array[i][j][k] = null;
      i_chandle_0d(chandle_array[3][2][1]);
      `CHECK_CHANDLE_VAL(chandle_array[3][2][1], get_non_null());
      i_chandle_1d(chandle_array[2][1]);
      `CHECK_CHANDLE_VAL(chandle_array[2][1][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[2][1][1], get_non_null());
      i_chandle_2d(chandle_array[1]);
      `CHECK_CHANDLE_VAL(chandle_array[1][0][1], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[1][1][1], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[1][2][1], get_non_null());
      i_chandle_3d(chandle_array);
      `CHECK_CHANDLE_VAL(chandle_array[0][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[1][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[2][0][0], get_non_null());
      `CHECK_CHANDLE_VAL(chandle_array[3][0][0], get_non_null());

      i_string_0d(string_array[3][2][1]);
      `CHECK_STRING_VAL(string_array[3][2][1], "42");
      i_string_1d(string_array[2][1]);
      `CHECK_STRING_VAL(string_array[2][1][0], "43");
      `CHECK_STRING_VAL(string_array[2][1][1], "44");
      i_string_2d(string_array[1]);
      `CHECK_STRING_VAL(string_array[1][0][1], "45");
      `CHECK_STRING_VAL(string_array[1][1][1], "46");
      `CHECK_STRING_VAL(string_array[1][2][1], "47");
      i_string_3d(string_array);
      `CHECK_STRING_VAL(string_array[0][0][0], "48");
      `CHECK_STRING_VAL(string_array[1][0][0], "49");
      `CHECK_STRING_VAL(string_array[2][0][0], "50");
      `CHECK_STRING_VAL(string_array[3][0][0], "51");

      i_bit1_0d(bit1_array[3][2][1]);
      `CHECK_0D(bit1_array[3][2][1]);
      i_bit1_1d(bit1_array[2][1]);
      `CHECK_1D(bit1_array[2][1]);
      i_bit1_2d(bit1_array[1]);
      `CHECK_2D(bit1_array[1]);
      i_bit1_3d(bit1_array);
      `CHECK_3D(bit1_array);

      i_bit7_0d(bit7_array[3][2][1]);
      `CHECK_0D(bit7_array[3][2][1]);
      i_bit7_1d(bit7_array[2][1]);
      `CHECK_1D(bit7_array[2][1]);
      i_bit7_2d(bit7_array[1]);
      `CHECK_2D(bit7_array[1]);
      i_bit7_3d(bit7_array);
      `CHECK_3D(bit7_array);

      i_bit121_0d(bit121_array[3][2][1]);
      `CHECK_0D(bit121_array[3][2][1]);
      i_bit121_1d(bit121_array[2][1]);
      `CHECK_1D(bit121_array[2][1]);
      i_bit121_2d(bit121_array[1]);
      `CHECK_2D(bit121_array[1]);
      i_bit121_3d(bit121_array);
      `CHECK_3D(bit121_array);

      i_logic1_0d(logic1_array[3][2][1]);
      `CHECK_0D(logic1_array[3][2][1]);
      i_logic1_1d(logic1_array[2][1]);
      `CHECK_1D(logic1_array[2][1]);
      i_logic1_2d(logic1_array[1]);
      `CHECK_2D(logic1_array[1]);
      i_logic1_3d(logic1_array);
      `CHECK_3D(logic1_array);

      i_logic7_0d(logic7_array[3][2][1]);
      `CHECK_0D(logic7_array[3][2][1]);
      i_logic7_1d(logic7_array[2][1]);
      `CHECK_1D(logic7_array[2][1]);
      i_logic7_2d(logic7_array[1]);
      `CHECK_2D(logic7_array[1]);
      i_logic7_3d(logic7_array);
      `CHECK_3D(logic7_array);

      i_logic121_0d(logic121_array[3][2][1]);
      `CHECK_0D(logic121_array[3][2][1]);
      i_logic121_1d(logic121_array[2][1]);
      `CHECK_1D(logic121_array[2][1]);
      i_logic121_2d(logic121_array[1]);
      `CHECK_2D(logic121_array[1]);
      i_logic121_3d(logic121_array);
      `CHECK_3D(logic121_array);

      i_pack_struct_0d(pack_struct_array[3][2][1]);
      `CHECK_0D(pack_struct_array[3][2][1]);
      i_pack_struct_1d(pack_struct_array[2][1]);
      `CHECK_1D(pack_struct_array[2][1]);
      i_pack_struct_2d(pack_struct_array[1]);
      `CHECK_2D(pack_struct_array[1]);
      i_pack_struct_3d(pack_struct_array);
      `CHECK_3D(pack_struct_array);

      `SET_VALUES(pack_struct_array);
      i_pack_struct_0d(pack_struct_array[3][2][1]);
      i_pack_struct_1d(pack_struct_array[2][1]);
      i_pack_struct_2d(pack_struct_array[1]);
      i_pack_struct_3d(pack_struct_array);

`ifndef NO_UNPACK_STRUCT
      i_unpack_struct_0d(unpack_struct_array[3][2][1]);
      `CHECK_VAL(unpack_struct_array[3][2][1].val, 42);

      i_unpack_struct_1d(unpack_struct_array[2][1]);
      `CHECK_VAL(unpack_struct_array[2][1][0].val, 43);
      `CHECK_VAL(unpack_struct_array[2][1][1].val, 44);

      i_unpack_struct_2d(unpack_struct_array[1]);
      `CHECK_VAL(unpack_struct_array[1][0][1].val, 45);
      `CHECK_VAL(unpack_struct_array[1][1][1].val, 46);
      `CHECK_VAL(unpack_struct_array[1][2][1].val, 47);

      i_unpack_struct_3d(unpack_struct_array);
      `CHECK_VAL(unpack_struct_array[0][0][0].val, 48);
      `CHECK_VAL(unpack_struct_array[1][0][0].val, 49);
      `CHECK_VAL(unpack_struct_array[2][0][0].val, 50);
      `CHECK_VAL(unpack_struct_array[3][0][0].val, 51);
`endif

      check_exports();
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
