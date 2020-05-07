// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
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
`endif

`ifdef VERILATOR
 `define NO_SHORTREAL
 `define NULL 64'd0
`else
 `define NULL null
`endif

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

`ifdef VERILATOR
   wire  _unused = &{1'b0, clk};
`endif

   // Legal input argument types for DPI functions

   //======================================================================
   // Type definitions
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.6
   typedef byte byte_t;
   typedef byte unsigned byte_unsigned_t;
   typedef shortint      shortint_t;
   typedef shortint unsigned shortint_unsigned_t;
   typedef int               int_t;
   typedef int unsigned      int_unsigned_t;
   typedef longint           longint_t;
   typedef longint unsigned  longint_unsigned_t;
`ifndef NO_TIME
   typedef time              time_t;
`endif
`ifndef NO_INTEGER
   typedef integer           integer_t;
`endif
   typedef real              real_t;
`ifndef NO_SHORTREAL
   typedef shortreal         shortreal_t;
`endif
   typedef chandle           chandle_t;
   typedef string            string_t;
   typedef bit               bit_t;
   typedef logic             logic_t;

   // 2-state packed structures
   typedef struct            packed { bit x; }                      struct_2_state_1;
   typedef struct            packed { bit [15:0] x; bit [15:0] y; } struct_2_state_32;
   typedef struct            packed { bit [15:0] x; bit [16:0] y; } struct_2_state_33;
   typedef struct            packed { bit [31:0] x; bit [31:0] y; } struct_2_state_64;
   typedef struct            packed { bit [31:0] x; bit [32:0] y; } struct_2_state_65;
   typedef struct            packed { bit [63:0] x; bit [63:0] y; } struct_2_state_128;

   // 2-state packed unions
   typedef union             packed { bit x; bit y; }                  union_2_state_1;
   typedef union             packed { bit [31:0] x; bit [31:0] y; }    union_2_state_32;
   typedef union             packed { bit [32:0] x; bit [32:0] y; }    union_2_state_33;
   typedef union             packed { bit [63:0] x; bit [63:0] y; }    union_2_state_64;
   typedef union             packed { bit [64:0] x; bit [64:0] y; }    union_2_state_65;
   typedef union             packed { bit [127:0] x; bit [127:0] y; }  union_2_state_128;

   // 4-state packed structures
   typedef struct            packed { logic x; }                      struct_4_state_1;
   typedef struct            packed { logic [15:0] x; bit [15:0] y; } struct_4_state_32;
   typedef struct            packed { logic [15:0] x; bit [16:0] y; } struct_4_state_33;
   typedef struct            packed { logic [31:0] x; bit [31:0] y; } struct_4_state_64;
   typedef struct            packed { logic [31:0] x; bit [32:0] y; } struct_4_state_65;
   typedef struct            packed { logic [63:0] x; bit [63:0] y; } struct_4_state_128;

   // 4-state packed unions
   typedef union             packed { logic x; bit y; }                  union_4_state_1;
   typedef union             packed { logic [31:0] x; bit [31:0] y; }    union_4_state_32;
   typedef union             packed { logic [32:0] x; bit [32:0] y; }    union_4_state_33;
   typedef union             packed { logic [63:0] x; bit [63:0] y; }    union_4_state_64;
   typedef union             packed { logic [64:0] x; bit [64:0] y; }    union_4_state_65;
   typedef union             packed { logic [127:0] x; bit [127:0] y; }  union_4_state_128;

   //======================================================================
   // Imports
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.6
   import "DPI-C" function void i_byte              (input byte              i);
   import "DPI-C" function void i_byte_unsigned     (input byte unsigned     i);
   import "DPI-C" function void i_shortint          (input shortint          i);
   import "DPI-C" function void i_shortint_unsigned (input shortint unsigned i);
   import "DPI-C" function void i_int               (input int               i);
   import "DPI-C" function void i_int_unsigned      (input int unsigned      i);
   import "DPI-C" function void i_longint           (input longint           i);
   import "DPI-C" function void i_longint_unsigned  (input longint unsigned  i);
`ifndef NO_TIME
   import "DPI-C" function void i_time              (input time              i);
`endif
`ifndef NO_INTEGER
   import "DPI-C" function void i_integer           (input integer           i);
`endif
   import "DPI-C" function void i_real              (input real              i);
`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal         (input shortreal         i);
`endif
   import "DPI-C" function void i_chandle           (input chandle           i);
   import "DPI-C" function void i_string            (input string            i);
   import "DPI-C" function void i_bit               (input bit               i);
   import "DPI-C" function void i_logic             (input logic             i);

   // Basic types via typedef
   import "DPI-C" function void i_byte_t              (input byte_t              i);
   import "DPI-C" function void i_byte_unsigned_t     (input byte_unsigned_t     i);
   import "DPI-C" function void i_shortint_t          (input shortint_t          i);
   import "DPI-C" function void i_shortint_unsigned_t (input shortint_unsigned_t i);
   import "DPI-C" function void i_int_t               (input int_t               i);
   import "DPI-C" function void i_int_unsigned_t      (input int_unsigned_t      i);
   import "DPI-C" function void i_longint_t           (input longint_t           i);
   import "DPI-C" function void i_longint_unsigned_t  (input longint_unsigned_t  i);
`ifndef NO_TIME
   import "DPI-C" function void i_time_t              (input time_t              i);
`endif
`ifndef NO_INTEGER
   import "DPI-C" function void i_integer_t           (input integer_t           i);
`endif
   import "DPI-C" function void i_real_t              (input real_t              i);
`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal_t         (input shortreal_t         i);
`endif
   import "DPI-C" function void i_chandle_t           (input chandle_t           i);
   import "DPI-C" function void i_string_t            (input string_t            i);
   import "DPI-C" function void i_bit_t               (input bit_t               i);
   import "DPI-C" function void i_logic_t             (input logic_t             i);

   // 2-state packed arrays
   import "DPI-C" function void i_array_2_state_1  (input bit [  0:0] i);
   import "DPI-C" function void i_array_2_state_32 (input bit [ 31:0] i);
   import "DPI-C" function void i_array_2_state_33 (input bit [ 32:0] i);
   import "DPI-C" function void i_array_2_state_64 (input bit [ 63:0] i);
   import "DPI-C" function void i_array_2_state_65 (input bit [ 64:0] i);
   import "DPI-C" function void i_array_2_state_128(input bit [127:0] i);

   // 2-state packed structures
   import "DPI-C" function void i_struct_2_state_1   (input struct_2_state_1   i);
   import "DPI-C" function void i_struct_2_state_32  (input struct_2_state_32  i);
   import "DPI-C" function void i_struct_2_state_33  (input struct_2_state_33  i);
   import "DPI-C" function void i_struct_2_state_64  (input struct_2_state_64  i);
   import "DPI-C" function void i_struct_2_state_65  (input struct_2_state_65  i);
   import "DPI-C" function void i_struct_2_state_128 (input struct_2_state_128 i);

   // 2-state packed unions
   import "DPI-C" function void i_union_2_state_1  (input union_2_state_1    i);
   import "DPI-C" function void i_union_2_state_32 (input union_2_state_32   i);
   import "DPI-C" function void i_union_2_state_33 (input union_2_state_33   i);
   import "DPI-C" function void i_union_2_state_64 (input union_2_state_64   i);
   import "DPI-C" function void i_union_2_state_65 (input union_2_state_65   i);
   import "DPI-C" function void i_union_2_state_128(input union_2_state_128  i);

   // 4-state packed arrays
   import "DPI-C" function void i_array_4_state_1  (input logic [  0:0] i);
   import "DPI-C" function void i_array_4_state_32 (input logic [ 31:0] i);
   import "DPI-C" function void i_array_4_state_33 (input logic [ 32:0] i);
   import "DPI-C" function void i_array_4_state_64 (input logic [ 63:0] i);
   import "DPI-C" function void i_array_4_state_65 (input logic [ 64:0] i);
   import "DPI-C" function void i_array_4_state_128(input logic [127:0] i);

   // 4-state packed structures
   import "DPI-C" function void i_struct_4_state_1   (input struct_4_state_1   i);
   import "DPI-C" function void i_struct_4_state_32  (input struct_4_state_32  i);
   import "DPI-C" function void i_struct_4_state_33  (input struct_4_state_33  i);
   import "DPI-C" function void i_struct_4_state_64  (input struct_4_state_64  i);
   import "DPI-C" function void i_struct_4_state_65  (input struct_4_state_65  i);
   import "DPI-C" function void i_struct_4_state_128 (input struct_4_state_128 i);

   // 4-state packed unions
   import "DPI-C" function void i_union_4_state_1  (input union_4_state_1    i);
   import "DPI-C" function void i_union_4_state_32 (input union_4_state_32   i);
   import "DPI-C" function void i_union_4_state_33 (input union_4_state_33   i);
   import "DPI-C" function void i_union_4_state_64 (input union_4_state_64   i);
   import "DPI-C" function void i_union_4_state_65 (input union_4_state_65   i);
   import "DPI-C" function void i_union_4_state_128(input union_4_state_128  i);

   //======================================================================
   // Exports
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.6
   export "DPI-C" function e_byte;
   export "DPI-C" function e_byte_unsigned;
   export "DPI-C" function e_shortint;
   export "DPI-C" function e_shortint_unsigned;
   export "DPI-C" function e_int;
   export "DPI-C" function e_int_unsigned;
   export "DPI-C" function e_longint;
   export "DPI-C" function e_longint_unsigned;
`ifndef NO_TIME
   export "DPI-C" function e_time;
`endif
`ifndef NO_INTEGER
   export "DPI-C" function e_integer;
`endif
   export "DPI-C" function e_real;
`ifndef NO_SHORTREAL
   export "DPI-C" function e_shortreal;
`endif
   export "DPI-C" function e_chandle;
   export "DPI-C" function e_string;
   export "DPI-C" function e_bit;
   export "DPI-C" function e_logic;

   // Basic types via typedef
   export "DPI-C" function e_byte_t;
   export "DPI-C" function e_byte_unsigned_t;
   export "DPI-C" function e_shortint_t;
   export "DPI-C" function e_shortint_unsigned_t;
   export "DPI-C" function e_int_t;
   export "DPI-C" function e_int_unsigned_t;
   export "DPI-C" function e_longint_t;
   export "DPI-C" function e_longint_unsigned_t;
`ifndef NO_TIME
   export "DPI-C" function e_time_t;
`endif
`ifndef NO_INTEGER
   export "DPI-C" function e_integer_t;
`endif
   export "DPI-C" function e_real_t;
`ifndef NO_SHORTREAL
   export "DPI-C" function e_shortreal_t;
`endif
   export "DPI-C" function e_chandle_t;
   export "DPI-C" function e_string_t;
   export "DPI-C" function e_bit_t;
   export "DPI-C" function e_logic_t;

   // 2-state packed arrays
   export "DPI-C" function e_array_2_state_1;
   export "DPI-C" function e_array_2_state_32;
   export "DPI-C" function e_array_2_state_33;
   export "DPI-C" function e_array_2_state_64;
   export "DPI-C" function e_array_2_state_65;
   export "DPI-C" function e_array_2_state_128;

   // 2-state packed structures
   export "DPI-C" function e_struct_2_state_1;
   export "DPI-C" function e_struct_2_state_32;
   export "DPI-C" function e_struct_2_state_33;
   export "DPI-C" function e_struct_2_state_64;
   export "DPI-C" function e_struct_2_state_65;
   export "DPI-C" function e_struct_2_state_128;

   // 2-state packed unions
   export "DPI-C" function e_union_2_state_1;
   export "DPI-C" function e_union_2_state_32;
   export "DPI-C" function e_union_2_state_33;
   export "DPI-C" function e_union_2_state_64;
   export "DPI-C" function e_union_2_state_65;
   export "DPI-C" function e_union_2_state_128;

   // 4-state packed arrays
   export "DPI-C" function e_array_4_state_1;
   export "DPI-C" function e_array_4_state_32;
   export "DPI-C" function e_array_4_state_33;
   export "DPI-C" function e_array_4_state_64;
   export "DPI-C" function e_array_4_state_65;
   export "DPI-C" function e_array_4_state_128;

   // 4-state packed structures
   export "DPI-C" function e_struct_4_state_1;
   export "DPI-C" function e_struct_4_state_32;
   export "DPI-C" function e_struct_4_state_33;
   export "DPI-C" function e_struct_4_state_64;
   export "DPI-C" function e_struct_4_state_65;
   export "DPI-C" function e_struct_4_state_128;

   // 4-state packed unions
   export "DPI-C" function e_union_4_state_1;
   export "DPI-C" function e_union_4_state_32;
   export "DPI-C" function e_union_4_state_33;
   export "DPI-C" function e_union_4_state_64;
   export "DPI-C" function e_union_4_state_65;
   export "DPI-C" function e_union_4_state_128;

   //======================================================================
   // Definitions of exported functions
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.6
   byte                      n_byte = 0;
   function void e_byte(input byte i);
      if (i !== 8'd10 + n_byte) $stop;
      n_byte++;
   endfunction

   byte                      n_byte_unsigned = 0;
   function void e_byte_unsigned(input byte unsigned i);
      if (i !== 8'd20 + n_byte_unsigned) $stop;
      n_byte_unsigned++;
   endfunction

   shortint                  n_shortint = 0;
   function void e_shortint(input shortint i);
      if (i !== 16'd30 + n_shortint) $stop;
      n_shortint++;
   endfunction

   shortint                  n_shortint_unsigned = 0;
   function void e_shortint_unsigned(input shortint unsigned i);
      if (i !== 16'd40 + n_shortint_unsigned) $stop;
      n_shortint_unsigned++;
   endfunction

   int                       n_int = 0;
   function void e_int(input int i);
      if (i !== 32'd50 + n_int) $stop;
      n_int++;
   endfunction

   int                       n_int_unsigned = 0;
   function void e_int_unsigned(input int unsigned i);
      if (i !== 32'd60 + n_int_unsigned) $stop;
      n_int_unsigned++;
   endfunction

   longint                   n_longint = 0;
   function void e_longint(input longint i);
      if (i !== 64'd70 + n_longint) $stop;
      n_longint++;
   endfunction

   longint                   n_longint_unsigned = 0;
   function void e_longint_unsigned(input longint unsigned i);
      if (i !== 64'd80 + n_longint_unsigned) $stop;
      n_longint_unsigned++;
   endfunction

`ifndef NO_TIME
   longint                   n_time = 0;
   function void e_time(input time i);
      if (i !== 64'd90 + n_time) $stop;
      n_time++;
   endfunction
`endif

`ifndef NO_INTEGER
   int                       n_integer = 0;
   function void e_integer(input integer i);
      if (i !== 32'd100 + n_integer) $stop;
      n_integer++;
   endfunction
`endif

   int                       n_real = 0;
   function void e_real(input real i);
      if (i != real'(2*n_real + 1) / 2.0) $stop;
      n_real++;
   endfunction

`ifndef NO_SHORTREAL
   int                       n_shortreal = 0;
   function void e_shortreal(input shortreal i);
      if (i != shortreal'(4*n_shortreal + 1)/ 4.0) $stop;
      n_shortreal++;
   endfunction
`endif

   int                       n_chandle = 0;
   function void e_chandle(input chandle i);
      $display("e_chandle %1d", n_chandle);
      if (!n_chandle[0]) begin
         if (i !== `NULL) $stop;
      end else begin
         if (i === `NULL) $stop;
      end
      n_chandle++;
   endfunction

   int n_string = 0;
   function void e_string(input string i);
      $display("e_string %1d", n_string);
      if (!n_string[0]) begin
         if (i != "Hello") $stop;
      end else begin
         if (i != "World") $stop;
      end
      n_string++;
   endfunction

   int n_bit = 0;
   function void e_bit(input bit i);
      $display("e_bit %1d", n_bit);
      if (i !== n_bit[0]) $stop;
      n_bit++;
   endfunction

   int n_logic = 0;
   function void e_logic(input logic i);
      $display("e_logic %1d", n_logic);
      if (i !== ~n_logic[0]) $stop;
      n_logic++;
   endfunction

   // Basic types via typedefs
   byte_t n_byte_t = 0;
   function void e_byte_t(input byte_t i);
      if (i !== 8'd10 + n_byte_t) $stop;
      n_byte_t += 2;
   endfunction

   byte n_byte_unsigned_t = 0;
   function void e_byte_unsigned_t(input byte_unsigned_t i);
      if (i !== 8'd20 + n_byte_unsigned_t) $stop;
      n_byte_unsigned_t += 2;
   endfunction

   shortint_t n_shortint_t = 0;
   function void e_shortint_t(input shortint_t i);
      if (i !== 16'd30 + n_shortint_t) $stop;
      n_shortint_t += 2;
   endfunction

   shortint n_shortint_unsigned_t = 0;
   function void e_shortint_unsigned_t(input shortint_unsigned_t i);
      if (i !== 16'd40 + n_shortint_unsigned_t) $stop;
      n_shortint_unsigned_t += 2;
   endfunction

   int_t n_int_t = 0;
   function void e_int_t(input int_t i);
      if (i !== 32'd50 + n_int_t) $stop;
      n_int_t += 2;
   endfunction

   int      n_int_unsigned_t = 0;
   function void e_int_unsigned_t(input int_unsigned_t i);
      if (i !== 32'd60 + n_int_unsigned_t) $stop;
      n_int_unsigned_t += 2;
   endfunction

   longint_t n_longint_t = 0;
   function void e_longint_t(input longint_t i);
      if (i !== 64'd70 + n_longint_t) $stop;
      n_longint_t += 2;
   endfunction

   longint  n_longint_unsigned_t = 0;
   function void e_longint_unsigned_t(input longint_unsigned_t i);
      if (i !== 64'd80 + n_longint_unsigned_t) $stop;
      n_longint_unsigned_t += 2;
   endfunction

`ifndef NO_TIME
   longint  n_time_t = 0;
   function void e_time_t(input time_t i);
      if (i !== 64'd90 + n_time_t) $stop;
      n_time_t += 2;
   endfunction
`endif

`ifndef NO_INTEGER
   int      n_integer_t = 0;
   function void e_integer_t(input integer_t i);
      if (i !== 32'd100 + n_integer_t) $stop;
      n_integer_t += 2;
   endfunction
`endif

   int      n_real_t = 0;
   function void e_real_t(input real_t i);
      if (i != real'(2*n_real_t + 1) / 2.0) $stop;
      n_real_t += 2;
   endfunction

`ifndef NO_SHORTREAL
   int      n_shortreal_t = 0;
   function void e_shortreal_t(input shortreal_t i);
      if (i != shortreal'(4*n_shortreal_t + 1)/ 4.0) $stop;
      n_shortreal_t += 2;
   endfunction
`endif

   int      n_chandle_t = 0;
   function void e_chandle_t(input chandle_t i);
      $display("e_chandle_t %1d", n_chandle_t);
      if (!n_chandle_t[0]) begin
         if (i === `NULL) $stop;
      end else begin
         if (i !== `NULL) $stop;
      end
      n_chandle_t++;
   endfunction

   int n_string_t = 0;
   function void e_string_t(input string_t i);
      $display("e_string_t %1d", n_string_t);
      if (!n_string_t[0]) begin
         if (i != "World") $stop;
      end else begin
         if (i != "Hello") $stop;
      end
      n_string_t++;
   endfunction

   int n_bit_t = 0;
   function void e_bit_t(input bit_t i);
      $display("e_bit_t %1d", n_bit_t);
      if (i !== n_bit_t[0]) $stop;
      n_bit_t++;
   endfunction

   int n_logic_t = 0;
   function void e_logic_t(input logic_t i);
      $display("e_logic_t %1d", n_logic_t);
      if (i !== ~n_logic_t[0]) $stop;
      n_logic_t++;
   endfunction

   // 2-state packed arrays
   int n_array_2_state_1 = 0;
   function void e_array_2_state_1(input bit [ 0:0] i);
      $display("e_array_2_state_1 %1d", n_array_2_state_1);
      if (i !== n_array_2_state_1[0]) $stop;
      n_array_2_state_1++;
   endfunction

   int n_array_2_state_32 = 0;
   function void e_array_2_state_32(input bit [31:0] i);
      $display("e_array_2_state_32 %1d", n_array_2_state_32);
      if (i !== ~32'd0 >> n_array_2_state_32) $stop;
      n_array_2_state_32++;
   endfunction

   int n_array_2_state_33 = 0;
   function void e_array_2_state_33(input bit [32:0] i);
      $display("e_array_2_state_33 %1d", n_array_2_state_33);
      if (i !== ~33'd0 >> n_array_2_state_33) $stop;
      n_array_2_state_33++;
   endfunction

   int n_array_2_state_64 = 0;
   function void e_array_2_state_64(input bit [63:0] i);
      $display("e_array_2_state_64 %1d", n_array_2_state_64);
      if (i !== ~64'd0 >> n_array_2_state_64) $stop;
      n_array_2_state_64++;
   endfunction

   int n_array_2_state_65 = 0;
   function void e_array_2_state_65(input bit [64:0] i);
      $display("e_array_2_state_65 %1d", n_array_2_state_65);
      if (i !== ~65'd0 >> n_array_2_state_65) $stop;
      n_array_2_state_65++;
   endfunction

   int n_array_2_state_128 = 0;
   function void e_array_2_state_128(input bit [127:0] i);
      $display("e_array_2_state_128 %1d", n_array_2_state_128);
      if (i !== ~128'd0 >> n_array_2_state_128) $stop;
      n_array_2_state_128++;
   endfunction

   // 2-state packed structures
   int n_struct_2_state_1 = 0;
   function void e_struct_2_state_1(input struct_2_state_1 i);
      $display("e_struct_2_state_1 %1d",  n_struct_2_state_1);
      if (i !== n_struct_2_state_1[0]) $stop;
      n_struct_2_state_1++;
   endfunction

   int n_struct_2_state_32 = 0;
   function void e_struct_2_state_32(input struct_2_state_32 i);
      $display("e_struct_2_state_32 %1d", n_struct_2_state_32);
      if (i !== ~32'd0 >> n_struct_2_state_32) $stop;
      n_struct_2_state_32++;
   endfunction

   int n_struct_2_state_33 = 0;
   function void e_struct_2_state_33(input struct_2_state_33 i);
      $display("e_struct_2_state_33 %1d", n_struct_2_state_33);
      if (i !== ~33'd0 >> n_struct_2_state_33) $stop;
      n_struct_2_state_33++;
   endfunction

   int n_struct_2_state_64 = 0;
   function void e_struct_2_state_64(input struct_2_state_64 i);
      $display("e_struct_2_state_64 %1d", n_struct_2_state_64);
      if (i !== ~64'd0 >> n_struct_2_state_64) $stop;
      n_struct_2_state_64++;
   endfunction

   int n_struct_2_state_65 = 0;
   function void e_struct_2_state_65(input struct_2_state_65 i);
      $display("e_struct_2_state_65 %1d", n_struct_2_state_65);
      if (i !== ~65'd0 >> n_struct_2_state_65) $stop;
      n_struct_2_state_65++;
   endfunction

   int n_struct_2_state_128 = 0;
   function void e_struct_2_state_128(input struct_2_state_128 i);
      $display("e_struct_2_state_128 %1d", n_struct_2_state_128);
      if (i !== ~128'd0 >> n_struct_2_state_128) $stop;
      n_struct_2_state_128++;
   endfunction

   // 2-state packed unions
   int n_union_2_state_1 = 0;
   function void e_union_2_state_1(input union_2_state_1 i);
      $display("e_union_2_state_1 %1d", n_union_2_state_1);
      if (i !== n_union_2_state_1[0]) $stop;
      n_union_2_state_1++;
   endfunction

   int n_union_2_state_32 = 0;
   function void e_union_2_state_32(input union_2_state_32 i);
      $display("e_union_2_state_32 %1d", n_union_2_state_32);
      if (i !== ~32'd0 >> n_union_2_state_32) $stop;
      n_union_2_state_32++;
   endfunction

   int n_union_2_state_33 = 0;
   function void e_union_2_state_33(input union_2_state_33 i);
      $display("e_union_2_state_33 %1d", n_union_2_state_33);
      if (i !== ~33'd0 >> n_union_2_state_33) $stop;
      n_union_2_state_33++;
   endfunction

   int n_union_2_state_64 = 0;
   function void e_union_2_state_64(input union_2_state_64 i);
      $display("e_union_2_state_64 %1d", n_union_2_state_64);
      if (i !== ~64'd0 >> n_union_2_state_64) $stop;
      n_union_2_state_64++;
   endfunction

   int n_union_2_state_65 = 0;
   function void e_union_2_state_65(input union_2_state_65 i);
      $display("e_union_2_state_65 %1d", n_union_2_state_65);
      if (i !== ~65'd0 >> n_union_2_state_65) $stop;
      n_union_2_state_65++;
   endfunction

   int n_union_2_state_128 = 0;
   function void e_union_2_state_128(input union_2_state_128 i);
      $display("e_union_2_state_128 %1d", n_union_2_state_128);
      if (i !== ~128'd0 >> n_union_2_state_128) $stop;
      n_union_2_state_128++;
   endfunction

   // 4-state packed arrays
   int n_array_4_state_1 = 0;
   function void e_array_4_state_1(input logic [ 0:0] i);
      $display("e_array_4_state_1 %1d", n_array_4_state_1);
      if (i !== n_array_4_state_1[0]) $stop;
      n_array_4_state_1++;
   endfunction

   int n_array_4_state_32 = 0;
   function void e_array_4_state_32(input logic [31:0] i);
      $display("e_array_4_state_32 %1d", n_array_4_state_32);
      if (i !== ~32'd0 >> n_array_4_state_32) $stop;
      n_array_4_state_32++;
   endfunction

   int n_array_4_state_33 = 0;
   function void e_array_4_state_33(input logic [32:0] i);
      $display("e_array_4_state_33 %1d", n_array_4_state_33);
      if (i !== ~33'd0 >> n_array_4_state_33) $stop;
      n_array_4_state_33++;
   endfunction

   int n_array_4_state_64 = 0;
   function void e_array_4_state_64(input logic [63:0] i);
      $display("e_array_4_state_64 %1d", n_array_4_state_64);
      if (i !== ~64'd0 >> n_array_4_state_64) $stop;
      n_array_4_state_64++;
   endfunction

   int n_array_4_state_65 = 0;
   function void e_array_4_state_65(input logic [64:0] i);
      $display("e_array_4_state_65 %1d", n_array_4_state_65);
      if (i !== ~65'd0 >> n_array_4_state_65) $stop;
      n_array_4_state_65++;
   endfunction

   int n_array_4_state_128 = 0;
   function void e_array_4_state_128(input logic [127:0] i);
      $display("e_array_4_state_128 %1d", n_array_4_state_128);
      if (i !== ~128'd0 >> n_array_4_state_128) $stop;
      n_array_4_state_128++;
   endfunction

   // 4-state packed structures
   int n_struct_4_state_1 = 0;
   function void e_struct_4_state_1(input struct_4_state_1 i);
      $display("e_struct_4_state_1 %1d",  n_struct_4_state_1);
      if (i !== n_struct_4_state_1[0]) $stop;
      n_struct_4_state_1++;
   endfunction

   int n_struct_4_state_32 = 0;
   function void e_struct_4_state_32(input struct_4_state_32 i);
      $display("e_struct_4_state_32 %1d", n_struct_4_state_32);
      if (i !== ~32'd0 >> n_struct_4_state_32) $stop;
      n_struct_4_state_32++;
   endfunction

   int n_struct_4_state_33 = 0;
   function void e_struct_4_state_33(input struct_4_state_33 i);
      $display("e_struct_4_state_33 %1d", n_struct_4_state_33);
      if (i !== ~33'd0 >> n_struct_4_state_33) $stop;
      n_struct_4_state_33++;
   endfunction

   int n_struct_4_state_64 = 0;
   function void e_struct_4_state_64(input struct_4_state_64 i);
      $display("e_struct_4_state_64 %1d", n_struct_4_state_64);
      if (i !== ~64'd0 >> n_struct_4_state_64) $stop;
      n_struct_4_state_64++;
   endfunction

   int n_struct_4_state_65 = 0;
   function void e_struct_4_state_65(input struct_4_state_65 i);
      $display("e_struct_4_state_65 %1d", n_struct_4_state_65);
      if (i !== ~65'd0 >> n_struct_4_state_65) $stop;
      n_struct_4_state_65++;
   endfunction

   int n_struct_4_state_128 = 0;
   function void e_struct_4_state_128(input struct_4_state_128 i);
      $display("e_struct_4_state_128 %1d", n_struct_4_state_128);
      if (i !== ~128'd0 >> n_struct_4_state_128) $stop;
      n_struct_4_state_128++;
   endfunction

   // 4-state packed unions
   int n_union_4_state_1 = 0;
   function void e_union_4_state_1(input union_4_state_1 i);
      $display("e_union_4_state_1 %1d", n_union_4_state_1);
      if (i !== n_union_4_state_1[0]) $stop;
      n_union_4_state_1++;
   endfunction

   int n_union_4_state_32 = 0;
   function void e_union_4_state_32(input union_4_state_32 i);
      $display("e_union_4_state_32 %1d", n_union_4_state_32);
      if (i !== ~32'd0 >> n_union_4_state_32) $stop;
      n_union_4_state_32++;
   endfunction

   int n_union_4_state_33 = 0;
   function void e_union_4_state_33(input union_4_state_33 i);
      $display("e_union_4_state_33 %1d", n_union_4_state_33);
      if (i !== ~33'd0 >> n_union_4_state_33) $stop;
      n_union_4_state_33++;
   endfunction

   int n_union_4_state_64 = 0;
   function void e_union_4_state_64(input union_4_state_64 i);
      $display("e_union_4_state_64 %1d", n_union_4_state_64);
      if (i !== ~64'd0 >> n_union_4_state_64) $stop;
      n_union_4_state_64++;
   endfunction

   int n_union_4_state_65 = 0;
   function void e_union_4_state_65(input union_4_state_65 i);
      $display("e_union_4_state_65 %1d", n_union_4_state_65);
      if (i !== ~65'd0 >> n_union_4_state_65) $stop;
      n_union_4_state_65++;
   endfunction

   int n_union_4_state_128 = 0;
   function void e_union_4_state_128(input union_4_state_128 i);
      $display("e_union_4_state_128 %1d", n_union_4_state_128);
      if (i !== ~128'd0 >> n_union_4_state_128) $stop;
      n_union_4_state_128++;
   endfunction

   //======================================================================
   // Invoke all functions 3 times (they have side effects)
   //======================================================================

   import "DPI-C" context function void check_exports();

   initial begin
      for (int i = 0 ; i < 3; i++) begin
         // Check the imports

         // Basic types as per IEEE 1800-2017 35.5.6
         i_byte(                8'd10 -  8'(i));
         i_byte_unsigned(       8'd20 -  8'(i));
         i_shortint(           16'd30 - 16'(i));
         i_shortint_unsigned(  16'd40 - 16'(i));
         i_int(                32'd50 - 32'(i));
         i_int_unsigned(       32'd60 - 32'(i));
         i_longint(            64'd70 - 64'(i));
         i_longint_unsigned(   64'd80 - 64'(i));
`ifndef NO_TIME
         i_time(               64'd90 - 64'(i));
`endif
`ifndef NO_INTEGER
         i_integer(            32'd100- 32'(i));
`endif
         i_real(               -1.0*i - 0.50);
`ifndef NO_SHORTREAL
         i_shortreal(          -1.0*i - 0.25);
`endif
         if (~i[0]) begin
            i_chandle(`NULL);
            i_string("World");
         end else begin
            i_chandle(`NULL);
            i_string("Hello");
         end
         i_bit(~i[0]);
         i_logic(i[0]);

         // Basic types via typedefs
         i_byte_t(                8'd10 -  8'(2*i));
         i_byte_unsigned_t(       8'd20 -  8'(2*i));
         i_shortint_t(           16'd30 - 16'(2*i));
         i_shortint_unsigned_t(  16'd40 - 16'(2*i));
         i_int_t(                32'd50 - 32'(2*i));
         i_int_unsigned_t(       32'd60 - 32'(2*i));
         i_longint_t(            64'd70 - 64'(2*i));
         i_longint_unsigned_t(   64'd80 - 64'(2*i));
`ifndef NO_TIME
         i_time_t(               64'd90 - 64'(2*i));
`endif
`ifndef NO_INTEGER
         i_integer_t(            32'd100- 32'(2*i));
`endif
         i_real_t(               -1.0*(2*i) - 0.50);
`ifndef NO_SHORTREAL
         i_shortreal_t(          -1.0*(2*i) - 0.25);
`endif
         if (~i[0]) begin
            i_chandle_t(`NULL);
            i_string_t("World");
         end else begin
            i_chandle_t(`NULL);
            i_string_t("Hello");
         end
         i_bit_t(~i[0]);
         i_logic_t(i[0]);

         // 2-state packed arrays
         i_array_2_state_1(~i[0]);
         i_array_2_state_32(~32'd0 << i);
         i_array_2_state_33(~33'd0 << i);
         i_array_2_state_64(~64'd0 << i);
         i_array_2_state_65(~65'd0 << i);
         i_array_2_state_128(~128'd0 << i);

         // 2-state packed structures
         i_struct_2_state_1(~i[0]);
         i_struct_2_state_32(~32'd0 << i);
         i_struct_2_state_33(~33'd0 << i);
         i_struct_2_state_64(~64'd0 << i);
         i_struct_2_state_65(~65'd0 << i);
         i_struct_2_state_128(~128'd0 << i);

         // 2-state packed unions
         i_union_2_state_1(~i[0]);
         i_union_2_state_32(~32'd0 << i);
         i_union_2_state_33(~33'd0 << i);
         i_union_2_state_64(~64'd0 << i);
         i_union_2_state_65(~65'd0 << i);
         i_union_2_state_128(~128'd0 << i);

         // 4-state packed arrays
         i_array_4_state_1(~i[0]);
         i_array_4_state_32(~32'd0 << i);
         i_array_4_state_33(~33'd0 << i);
         i_array_4_state_64(~64'd0 << i);
         i_array_4_state_65(~65'd0 << i);
         i_array_4_state_128(~128'd0 << i);

         // 4-state packed structures
         i_struct_4_state_1(~i[0]);
         i_struct_4_state_32(~32'd0 << i);
         i_struct_4_state_33(~33'd0 << i);
         i_struct_4_state_64(~64'd0 << i);
         i_struct_4_state_65(~65'd0 << i);
         i_struct_4_state_128(~128'd0 << i);

         // 4-state packed unions
         i_union_4_state_1(~i[0]);
         i_union_4_state_32(~32'd0 << i);
         i_union_4_state_33(~33'd0 << i);
         i_union_4_state_64(~64'd0 << i);
         i_union_4_state_65(~65'd0 << i);
         i_union_4_state_128(~128'd0 << i);

         // Check the exports
         check_exports();
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
