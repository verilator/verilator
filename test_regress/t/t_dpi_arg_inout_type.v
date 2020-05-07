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

   // Legal inout argument types for DPI functions

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
   import "DPI-C" function void i_byte              (inout byte              x);
   import "DPI-C" function void i_byte_unsigned     (inout byte unsigned     x);
   import "DPI-C" function void i_shortint          (inout shortint          x);
   import "DPI-C" function void i_shortint_unsigned (inout shortint unsigned x);
   import "DPI-C" function void i_int               (inout int               x);
   import "DPI-C" function void i_int_unsigned      (inout int unsigned      x);
   import "DPI-C" function void i_longint           (inout longint           x);
   import "DPI-C" function void i_longint_unsigned  (inout longint unsigned  x);
`ifndef NO_TIME
   import "DPI-C" function void i_time              (inout time              x);
`endif
`ifndef NO_INTEGER
   import "DPI-C" function void i_integer           (inout integer           x);
`endif
   import "DPI-C" function void i_real              (inout real              x);
`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal         (inout shortreal         x);
`endif
   import "DPI-C" function void i_chandle           (inout chandle           x);
   import "DPI-C" function void i_string            (inout string            x);
   import "DPI-C" function void i_bit               (inout bit               x);
   import "DPI-C" function void i_logic             (inout logic             x);

   // Basic types via typedef
   import "DPI-C" function void i_byte_t              (inout byte_t              x);
   import "DPI-C" function void i_byte_unsigned_t     (inout byte_unsigned_t     x);
   import "DPI-C" function void i_shortint_t          (inout shortint_t          x);
   import "DPI-C" function void i_shortint_unsigned_t (inout shortint_unsigned_t x);
   import "DPI-C" function void i_int_t               (inout int_t               x);
   import "DPI-C" function void i_int_unsigned_t      (inout int_unsigned_t      x);
   import "DPI-C" function void i_longint_t           (inout longint_t           x);
   import "DPI-C" function void i_longint_unsigned_t  (inout longint_unsigned_t  x);
`ifndef NO_TIME
   import "DPI-C" function void i_time_t              (inout time_t              x);
`endif
`ifndef NO_INTEGER
   import "DPI-C" function void i_integer_t           (inout integer_t           x);
`endif
   import "DPI-C" function void i_real_t              (inout real_t              x);
`ifndef NO_SHORTREAL
   import "DPI-C" function void i_shortreal_t         (inout shortreal_t         x);
`endif
   import "DPI-C" function void i_chandle_t           (inout chandle_t           x);
   import "DPI-C" function void i_string_t            (inout string_t            x);
   import "DPI-C" function void i_bit_t               (inout bit_t               x);
   import "DPI-C" function void i_logic_t             (inout logic_t             x);

   // 2-state packed arrays
   import "DPI-C" function void i_array_2_state_1  (inout bit [  0:0] x);
   import "DPI-C" function void i_array_2_state_32 (inout bit [ 31:0] x);
   import "DPI-C" function void i_array_2_state_33 (inout bit [ 32:0] x);
   import "DPI-C" function void i_array_2_state_64 (inout bit [ 63:0] x);
   import "DPI-C" function void i_array_2_state_65 (inout bit [ 64:0] x);
   import "DPI-C" function void i_array_2_state_128(inout bit [127:0] x);

   // 2-state packed structures
   import "DPI-C" function void i_struct_2_state_1   (inout struct_2_state_1    x);
   import "DPI-C" function void i_struct_2_state_32  (inout struct_2_state_32   x);
   import "DPI-C" function void i_struct_2_state_33  (inout struct_2_state_33   x);
   import "DPI-C" function void i_struct_2_state_64  (inout struct_2_state_64   x);
   import "DPI-C" function void i_struct_2_state_65  (inout struct_2_state_65   x);
   import "DPI-C" function void i_struct_2_state_128 (inout struct_2_state_128  x);

   // 2-state packed unions
   import "DPI-C" function void i_union_2_state_1    (inout union_2_state_1   x);
   import "DPI-C" function void i_union_2_state_32   (inout union_2_state_32  x);
   import "DPI-C" function void i_union_2_state_33   (inout union_2_state_33  x);
   import "DPI-C" function void i_union_2_state_64   (inout union_2_state_64  x);
   import "DPI-C" function void i_union_2_state_65   (inout union_2_state_65  x);
   import "DPI-C" function void i_union_2_state_128  (inout union_2_state_128 x);

   // 4-state packed arrays
   import "DPI-C" function void i_array_4_state_1  (inout logic [  0:0] x);
   import "DPI-C" function void i_array_4_state_32 (inout logic [ 31:0] x);
   import "DPI-C" function void i_array_4_state_33 (inout logic [ 32:0] x);
   import "DPI-C" function void i_array_4_state_64 (inout logic [ 63:0] x);
   import "DPI-C" function void i_array_4_state_65 (inout logic [ 64:0] x);
   import "DPI-C" function void i_array_4_state_128(inout logic [127:0] x);

   // 4-state packed structures
   import "DPI-C" function void i_struct_4_state_1   (inout struct_4_state_1    x);
   import "DPI-C" function void i_struct_4_state_32  (inout struct_4_state_32   x);
   import "DPI-C" function void i_struct_4_state_33  (inout struct_4_state_33   x);
   import "DPI-C" function void i_struct_4_state_64  (inout struct_4_state_64   x);
   import "DPI-C" function void i_struct_4_state_65  (inout struct_4_state_65   x);
   import "DPI-C" function void i_struct_4_state_128 (inout struct_4_state_128  x);

   // 4-state packed unions
   import "DPI-C" function void i_union_4_state_1    (inout union_4_state_1   x);
   import "DPI-C" function void i_union_4_state_32   (inout union_4_state_32  x);
   import "DPI-C" function void i_union_4_state_33   (inout union_4_state_33  x);
   import "DPI-C" function void i_union_4_state_64   (inout union_4_state_64  x);
   import "DPI-C" function void i_union_4_state_65   (inout union_4_state_65  x);
   import "DPI-C" function void i_union_4_state_128  (inout union_4_state_128 x);

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
   function void e_byte(inout byte x);
      if (x !== 8'd10 + n_byte) $stop;
      x += 8'd100;
      n_byte++;
   endfunction

   byte                      n_byte_unsigned = 0;
   function void e_byte_unsigned(inout byte unsigned x);
      if (x !== 8'd20 + n_byte_unsigned) $stop;
      x += 8'd200;
      n_byte_unsigned++;
   endfunction

   shortint                  n_shortint = 0;
   function void e_shortint(inout shortint x);
      if (x !== 16'd30 + n_shortint) $stop;
      x += 16'd300;
      n_shortint++;
   endfunction

   shortint                  n_shortint_unsigned = 0;
   function void e_shortint_unsigned(inout shortint unsigned x);
      if (x !== 16'd40 + n_shortint_unsigned) $stop;
      x += 16'd400;
      n_shortint_unsigned++;
   endfunction

   int                       n_int = 0;
   function void e_int(inout int x);
      if (x !== 32'd50 + n_int) $stop;
      x += 32'd500;
      n_int++;
   endfunction

   int                       n_int_unsigned = 0;
   function void e_int_unsigned(inout int unsigned x);
      if (x !== 32'd60 + n_int_unsigned) $stop;
      x += 32'd600;
      n_int_unsigned++;
   endfunction

   longint                   n_longint = 0;
   function void e_longint(inout longint x);
      if (x !== 64'd70 + n_longint) $stop;
      x += 64'd700;
      n_longint++;
   endfunction

   longint                   n_longint_unsigned = 0;
   function void e_longint_unsigned(inout longint unsigned x);
      if (x !== 64'd80 + n_longint_unsigned) $stop;
      x += 64'd800;
      n_longint_unsigned++;
   endfunction

`ifndef NO_TIME
   longint                   n_time = 0;
   function void e_time(inout time x);
      if (x !== 64'd90 + n_time) $stop;
      x += 64'd900;
      n_time++;
   endfunction
`endif

`ifndef NO_INTEGER
   int                       n_integer = 0;
   function void e_integer(inout integer x);
      if (x !== 32'd100 + n_integer) $stop;
      x += 32'd1000;
      n_integer++;
   endfunction
`endif

   int                       n_real = 0;
   function void e_real(inout real x);
      if (x != real'(2*n_real + 1) / 2.0) $stop;
      x += 100.0;
      n_real++;
   endfunction

`ifndef NO_SHORTREAL
   int                       n_shortreal = 0;
   function void e_shortreal(inout shortreal x);
      if (x != shortreal'(4*n_shortreal + 1)/ 4.0) $stop;
      x += 200.0;
      n_shortreal++;
   endfunction
`endif

   int                       n_chandle = 0;
   function void e_chandle(inout chandle x);
      $display("e_chandle %1d", n_chandle);
      if (!n_chandle[0]) begin
         if (x === `NULL) $stop;
      end else begin
         if (x !== `NULL) $stop;
      end
      x = `NULL;
      n_chandle++;
   endfunction

   int n_string = 0;
   function void e_string(inout string x);
      $display("e_string %1d", n_string);
      if (!n_string[0]) begin
         if (x != "Good") $stop;
         x = "Hello";
      end else begin
         if (x != "Bye") $stop;
         x = "World";
      end
      n_string++;
   endfunction

   int n_bit = 0;
   function void e_bit(inout bit x);
      $display("e_bit %1d", n_bit);
      if (x !== n_bit[0]) $stop;
      x = ~x;
      n_bit++;
   endfunction

   int n_logic = 0;
   function void e_logic(inout logic x);
      $display("e_logic %1d", n_logic);
      if (x !== ~n_logic[0]) $stop;
      x = ~x;
      n_logic++;
   endfunction

   // Basic types via typedefs
   byte_t n_byte_t = 0;
   function void e_byte_t(inout byte_t x);
      if (x !== 8'd10 + n_byte_t) $stop;
      x += 8'd101;
      n_byte_t += 2;
   endfunction

   byte n_byte_unsigned_t = 0;
   function void e_byte_unsigned_t(inout byte_unsigned_t x);
      if (x !== 8'd20 + n_byte_unsigned_t) $stop;
      x += 8'd202;
      n_byte_unsigned_t += 2;
   endfunction

   shortint_t n_shortint_t = 0;
   function void e_shortint_t(inout shortint_t x);
      if (x !== 16'd30 + n_shortint_t) $stop;
      x += 16'd303;
      n_shortint_t += 2;
   endfunction

   shortint n_shortint_unsigned_t = 0;
   function void e_shortint_unsigned_t(inout shortint_unsigned_t x);
      if (x !== 16'd40 + n_shortint_unsigned_t) $stop;
      x += 16'd404;
      n_shortint_unsigned_t += 2;
   endfunction

   int_t n_int_t = 0;
   function void e_int_t(inout int_t x);
      if (x !== 32'd50 + n_int_t) $stop;
      x += 32'd505;
      n_int_t += 2;
   endfunction

   int      n_int_unsigned_t = 0;
   function void e_int_unsigned_t(inout int_unsigned_t x);
      if (x !== 32'd60 + n_int_unsigned_t) $stop;
      x += 32'd606;
      n_int_unsigned_t += 2;
   endfunction

   longint_t n_longint_t = 0;
   function void e_longint_t(inout longint_t x);
      if (x !== 64'd70 + n_longint_t) $stop;
      x += 64'd707;
      n_longint_t += 2;
   endfunction

   longint  n_longint_unsigned_t = 0;
   function void e_longint_unsigned_t(inout longint_unsigned_t x);
      if (x !== 64'd80 + n_longint_unsigned_t) $stop;
      x += 64'd808;
      n_longint_unsigned_t += 2;
   endfunction

`ifndef NO_TIME
   longint  n_time_t = 0;
   function void e_time_t(inout time_t x);
      if (x !== 64'd90 + n_time_t) $stop;
      x += 64'd909;
      n_time_t += 2;
   endfunction
`endif

`ifndef NO_INTEGER
   int      n_integer_t = 0;
   function void e_integer_t(inout integer_t x);
      if (x !== 32'd100 + n_integer_t) $stop;
      x += 32'd1001;
      n_integer_t += 2;
   endfunction
`endif

   int      n_real_t = 0;
   function void e_real_t(inout real_t x);
      if (x != real'(2*n_real_t + 1) / 2.0) $stop;
      x += 111.0;
      n_real_t += 2;
   endfunction

`ifndef NO_SHORTREAL
   int      n_shortreal_t = 0;
   function void e_shortreal_t(inout shortreal_t x);
      if (x != shortreal'(4*n_shortreal_t + 1)/ 4.0) $stop;
      x += 222.0;
      n_shortreal_t += 2;
   endfunction
`endif

   int      n_chandle_t = 0;
   function void e_chandle_t(inout chandle_t x);
      $display("e_chandle_t %1d", n_chandle_t);
      if (!n_chandle_t[0]) begin
         if (x !== `NULL) $stop;
      end else begin
         if (x === `NULL) $stop;
      end
      x = `NULL;
      n_chandle_t++;
   endfunction

   int n_string_t = 0;
   function void e_string_t(inout string_t x);
      $display("e_string_t %1d", n_string_t);
      if (!n_string_t[0]) begin
         if (x != "Bye") $stop;
         x = "World";
      end else begin
         if (x != "Good") $stop;
         x = "Hello";
      end
      n_string_t++;
   endfunction

   int n_bit_t = 0;
   function void e_bit_t(inout bit_t x);
      $display("e_bit_t %1d", n_bit_t);
      if (x !== n_bit_t[0]) $stop;
      x = ~x;
      n_bit_t++;
   endfunction

   int n_logic_t = 0;
   function void e_logic_t(inout logic_t x);
      $display("e_logic_t %1d", n_logic_t);
      if (x !== ~n_logic_t[0]) $stop;
      x = ~x;
      n_logic_t++;
   endfunction

   // 2-state packed arrays
   int n_array_2_state_1 = 0;
   function void e_array_2_state_1(inout bit [ 0:0] x);
      $display("e_array_2_state_1 %1d", n_array_2_state_1);
      if (x !== n_array_2_state_1[0]) $stop;
      x = ~x;
      n_array_2_state_1++;
   endfunction

   int n_array_2_state_32 = 0;
   function void e_array_2_state_32(inout bit [31:0] x);
      $display("e_array_2_state_32 %1d", n_array_2_state_32);
      if (x !== ~32'd0 >> n_array_2_state_32) $stop;
      x <<= n_array_2_state_32;
      n_array_2_state_32++;
   endfunction

   int n_array_2_state_33 = 0;
   function void e_array_2_state_33(inout bit [32:0] x);
      $display("e_array_2_state_33 %1d", n_array_2_state_33);
      if (x !== ~33'd0 >> n_array_2_state_33) $stop;
      x <<= n_array_2_state_33;
      n_array_2_state_33++;
   endfunction

   int n_array_2_state_64 = 0;
   function void e_array_2_state_64(inout bit [63:0] x);
      $display("e_array_2_state_64 %1d", n_array_2_state_64);
      if (x !== ~64'd0 >> n_array_2_state_64) $stop;
      x <<= n_array_2_state_64;
      n_array_2_state_64++;
   endfunction

   int n_array_2_state_65 = 0;
   function void e_array_2_state_65(inout bit [64:0] x);
      $display("e_array_2_state_65 %1d", n_array_2_state_65);
      if (x !== ~65'd0 >> n_array_2_state_65) $stop;
      x <<= n_array_2_state_65;
      n_array_2_state_65++;
   endfunction

   int n_array_2_state_128 = 0;
   function void e_array_2_state_128(inout bit [127:0] x);
      $display("e_array_2_state_128 %1d", n_array_2_state_128);
      if (x !== ~128'd0 >> n_array_2_state_128) $stop;
      x <<= n_array_2_state_128;
      n_array_2_state_128++;
   endfunction

   // 2-state packed structures
   int n_struct_2_state_1 = 0;
   function void e_struct_2_state_1(inout struct_2_state_1 x);
      $display("e_struct_2_state_1 %1d",  n_struct_2_state_1);
      if (x !== n_struct_2_state_1[0]) $stop;
      x = ~x;
      n_struct_2_state_1++;
   endfunction

   int n_struct_2_state_32 = 0;
   function void e_struct_2_state_32(inout struct_2_state_32 x);
      $display("e_struct_2_state_32 %1d", n_struct_2_state_32);
      if (x !== ~32'd0 >> n_struct_2_state_32) $stop;
      x <<= n_struct_2_state_32;
      n_struct_2_state_32++;
   endfunction

   int n_struct_2_state_33 = 0;
   function void e_struct_2_state_33(inout struct_2_state_33 x);
      $display("e_struct_2_state_33 %1d", n_struct_2_state_33);
      if (x !== ~33'd0 >> n_struct_2_state_33) $stop;
      x <<= n_struct_2_state_33;
      n_struct_2_state_33++;
   endfunction

   int n_struct_2_state_64 = 0;
   function void e_struct_2_state_64(inout struct_2_state_64 x);
      $display("e_struct_2_state_64 %1d", n_struct_2_state_64);
      if (x !== ~64'd0 >> n_struct_2_state_64) $stop;
      x <<= n_struct_2_state_64;
      n_struct_2_state_64++;
   endfunction

   int n_struct_2_state_65 = 0;
   function void e_struct_2_state_65(inout struct_2_state_65 x);
      $display("e_struct_2_state_65 %1d", n_struct_2_state_65);
      if (x !== ~65'd0 >> n_struct_2_state_65) $stop;
      x <<= n_struct_2_state_65;
      n_struct_2_state_65++;
   endfunction

   int n_struct_2_state_128 = 0;
   function void e_struct_2_state_128(inout struct_2_state_128 x);
      $display("e_struct_2_state_128 %1d", n_struct_2_state_128);
      if (x !== ~128'd0 >> n_struct_2_state_128) $stop;
      x <<= n_struct_2_state_128;
      n_struct_2_state_128++;
   endfunction

   // 2-state packed unions
   int n_union_2_state_1 = 0;
   function void e_union_2_state_1(inout union_2_state_1 x);
      $display("e_union_2_state_1 %1d", n_union_2_state_1);
      if (x !== n_union_2_state_1[0]) $stop;
      x = ~x;
      n_union_2_state_1++;
   endfunction

   int n_union_2_state_32 = 0;
   function void e_union_2_state_32(inout union_2_state_32 x);
      $display("e_union_2_state_32 %1d", n_union_2_state_32);
      if (x !== ~32'd0 >> n_union_2_state_32) $stop;
      x <<= n_union_2_state_32;
      n_union_2_state_32++;
   endfunction

   int n_union_2_state_33 = 0;
   function void e_union_2_state_33(inout union_2_state_33 x);
      $display("e_union_2_state_33 %1d", n_union_2_state_33);
      if (x !== ~33'd0 >> n_union_2_state_33) $stop;
      x <<= n_union_2_state_33;
      n_union_2_state_33++;
   endfunction

   int n_union_2_state_64 = 0;
   function void e_union_2_state_64(inout union_2_state_64 x);
      $display("e_union_2_state_64 %1d", n_union_2_state_64);
      if (x !== ~64'd0 >> n_union_2_state_64) $stop;
      x <<= n_union_2_state_64;
      n_union_2_state_64++;
   endfunction

   int n_union_2_state_65 = 0;
   function void e_union_2_state_65(inout union_2_state_65 x);
      $display("e_union_2_state_65 %1d", n_union_2_state_65);
      if (x !== ~65'd0 >> n_union_2_state_65) $stop;
      x <<= n_union_2_state_65;
      n_union_2_state_65++;
   endfunction

   int n_union_2_state_128 = 0;
   function void e_union_2_state_128(inout union_2_state_128 x);
      $display("e_union_2_state_128 %1d", n_union_2_state_128);
      if (x !== ~128'd0 >> n_union_2_state_128) $stop;
      x <<= n_union_2_state_128;
      n_union_2_state_128++;
   endfunction

   // 4-state packed arrays
   int n_array_4_state_1 = 0;
   function void e_array_4_state_1(inout logic [ 0:0] x);
      $display("e_array_4_state_1 %1d", n_array_4_state_1);
      if (x !== n_array_4_state_1[0]) $stop;
      x = ~x;
      n_array_4_state_1++;
   endfunction

   int n_array_4_state_32 = 0;
   function void e_array_4_state_32(inout logic [31:0] x);
      $display("e_array_4_state_32 %1d", n_array_4_state_32);
      if (x !== ~32'd0 >> n_array_4_state_32) $stop;
      x <<= n_array_4_state_32;
      n_array_4_state_32++;
   endfunction

   int n_array_4_state_33 = 0;
   function void e_array_4_state_33(inout logic [32:0] x);
      $display("e_array_4_state_33 %1d", n_array_4_state_33);
      if (x !== ~33'd0 >> n_array_4_state_33) $stop;
      x <<= n_array_4_state_33;
      n_array_4_state_33++;
   endfunction

   int n_array_4_state_64 = 0;
   function void e_array_4_state_64(inout logic [63:0] x);
      $display("e_array_4_state_64 %1d", n_array_4_state_64);
      if (x !== ~64'd0 >> n_array_4_state_64) $stop;
      x <<= n_array_4_state_64;
      n_array_4_state_64++;
   endfunction

   int n_array_4_state_65 = 0;
   function void e_array_4_state_65(inout logic [64:0] x);
      $display("e_array_4_state_65 %1d", n_array_4_state_65);
      if (x !== ~65'd0 >> n_array_4_state_65) $stop;
      x <<= n_array_4_state_65;
      n_array_4_state_65++;
   endfunction

   int n_array_4_state_128 = 0;
   function void e_array_4_state_128(inout logic [127:0] x);
      $display("e_array_4_state_128 %1d", n_array_4_state_128);
      if (x !== ~128'd0 >> n_array_4_state_128) $stop;
      x <<= n_array_4_state_128;
      n_array_4_state_128++;
   endfunction

   // 4-state packed structures
   int n_struct_4_state_1 = 0;
   function void e_struct_4_state_1(inout struct_4_state_1 x);
      $display("e_struct_4_state_1 %1d",  n_struct_4_state_1);
      if (x !== n_struct_4_state_1[0]) $stop;
      x = ~x;
      n_struct_4_state_1++;
   endfunction

   int n_struct_4_state_32 = 0;
   function void e_struct_4_state_32(inout struct_4_state_32 x);
      $display("e_struct_4_state_32 %1d", n_struct_4_state_32);
      if (x !== ~32'd0 >> n_struct_4_state_32) $stop;
      x <<= n_struct_4_state_32;
      n_struct_4_state_32++;
   endfunction

   int n_struct_4_state_33 = 0;
   function void e_struct_4_state_33(inout struct_4_state_33 x);
      $display("e_struct_4_state_33 %1d", n_struct_4_state_33);
      if (x !== ~33'd0 >> n_struct_4_state_33) $stop;
      x <<= n_struct_4_state_33;
      n_struct_4_state_33++;
   endfunction

   int n_struct_4_state_64 = 0;
   function void e_struct_4_state_64(inout struct_4_state_64 x);
      $display("e_struct_4_state_64 %1d", n_struct_4_state_64);
      if (x !== ~64'd0 >> n_struct_4_state_64) $stop;
      x <<= n_struct_4_state_64;
      n_struct_4_state_64++;
   endfunction

   int n_struct_4_state_65 = 0;
   function void e_struct_4_state_65(inout struct_4_state_65 x);
      $display("e_struct_4_state_65 %1d", n_struct_4_state_65);
      if (x !== ~65'd0 >> n_struct_4_state_65) $stop;
      x <<= n_struct_4_state_65;
      n_struct_4_state_65++;
   endfunction

   int n_struct_4_state_128 = 0;
   function void e_struct_4_state_128(inout struct_4_state_128 x);
      $display("e_struct_4_state_128 %1d", n_struct_4_state_128);
      if (x !== ~128'd0 >> n_struct_4_state_128) $stop;
      x <<= n_struct_4_state_128;
      n_struct_4_state_128++;
   endfunction

   // 4-state packed unions
   int n_union_4_state_1 = 0;
   function void e_union_4_state_1(inout union_4_state_1 x);
      $display("e_union_4_state_1 %1d", n_union_4_state_1);
      if (x !== n_union_4_state_1[0]) $stop;
      x = ~x;
      n_union_4_state_1++;
   endfunction

   int n_union_4_state_32 = 0;
   function void e_union_4_state_32(inout union_4_state_32 x);
      $display("e_union_4_state_32 %1d", n_union_4_state_32);
      if (x !== ~32'd0 >> n_union_4_state_32) $stop;
      x <<= n_union_4_state_32;
      n_union_4_state_32++;
   endfunction

   int n_union_4_state_33 = 0;
   function void e_union_4_state_33(inout union_4_state_33 x);
      $display("e_union_4_state_33 %1d", n_union_4_state_33);
      if (x !== ~33'd0 >> n_union_4_state_33) $stop;
      x <<= n_union_4_state_33;
      n_union_4_state_33++;
   endfunction

   int n_union_4_state_64 = 0;
   function void e_union_4_state_64(inout union_4_state_64 x);
      $display("e_union_4_state_64 %1d", n_union_4_state_64);
      if (x !== ~64'd0 >> n_union_4_state_64) $stop;
      x <<= n_union_4_state_64;
      n_union_4_state_64++;
   endfunction

   int n_union_4_state_65 = 0;
   function void e_union_4_state_65(inout union_4_state_65 x);
      $display("e_union_4_state_65 %1d", n_union_4_state_65);
      if (x !== ~65'd0 >> n_union_4_state_65) $stop;
      x <<= n_union_4_state_65;
      n_union_4_state_65++;
   endfunction

   int n_union_4_state_128 = 0;
   function void e_union_4_state_128(inout union_4_state_128 x);
      $display("e_union_4_state_128 %1d", n_union_4_state_128);
      if (x !== ~128'd0 >> n_union_4_state_128) $stop;
      x <<= n_union_4_state_128;
      n_union_4_state_128++;
   endfunction

   //======================================================================
   // Invoke all functions 3 times (they have side effects)
   //======================================================================

   import "DPI-C" context function void check_exports();

   initial begin
      for (int i = 0 ; i < 3; i++) begin
         // Check the imports

         byte              x_byte;
         byte unsigned     x_byte_unsigned;
         shortint          x_shortint;
         shortint unsigned x_shortint_unsigned;
         int               x_int;
         int unsigned      x_int_unsigned;
         longint           x_longint;
         longint unsigned  x_longint_unsigned;
`ifndef NO_TIME
         time              x_time;
`endif
`ifndef NO_INTEGER
         integer           x_integer;
`endif
         real              x_real;
`ifndef NO_SHORTREAL
         shortreal         x_shortreal;
`endif
         chandle           x_chandle;
         string            x_string;
         bit               x_bit;
         logic             x_logic;

         byte_t              x_byte_t;
         byte_unsigned_t     x_byte_unsigned_t;
         shortint_t          x_shortint_t;
         shortint_unsigned_t x_shortint_unsigned_t;
         int_t               x_int_t;
         int_unsigned_t      x_int_unsigned_t;
         longint_t           x_longint_t;
         longint_unsigned_t  x_longint_unsigned_t;
`ifndef NO_TIME
         time_t              x_time_t;
`endif
`ifndef NO_INTEGER
         integer_t           x_integer_t;
`endif
         real_t              x_real_t;
`ifndef NO_SHORTREAL
         shortreal_t         x_shortreal_t;
`endif
         chandle_t           x_chandle_t;
         string_t            x_string_t;
         bit_t               x_bit_t;
         logic_t             x_logic_t;

         bit [  0:0]       x_bit_1;
         bit [ 31:0]       x_bit_32;
         bit [ 32:0]       x_bit_33;
         bit [ 63:0]       x_bit_64;
         bit [ 64:0]       x_bit_65;
         bit [127:0]       x_bit_128;

         struct_2_state_1  x_struct_2_state_1;
         struct_2_state_32 x_struct_2_state_32;
         struct_2_state_33 x_struct_2_state_33;
         struct_2_state_64 x_struct_2_state_64;
         struct_2_state_65 x_struct_2_state_65;
         struct_2_state_128 x_struct_2_state_128;

         union_2_state_1  x_union_2_state_1;
         union_2_state_32 x_union_2_state_32;
         union_2_state_33 x_union_2_state_33;
         union_2_state_64 x_union_2_state_64;
         union_2_state_65 x_union_2_state_65;
         union_2_state_128 x_union_2_state_128;

         logic [  0:0]     x_logic_1;
         logic [ 31:0]     x_logic_32;
         logic [ 32:0]     x_logic_33;
         logic [ 63:0]     x_logic_64;
         logic [ 64:0]     x_logic_65;
         logic [127:0]     x_logic_128;

         struct_4_state_1  x_struct_4_state_1;
         struct_4_state_32 x_struct_4_state_32;
         struct_4_state_33 x_struct_4_state_33;
         struct_4_state_64 x_struct_4_state_64;
         struct_4_state_65 x_struct_4_state_65;
         struct_4_state_128 x_struct_4_state_128;

         union_4_state_1  x_union_4_state_1;
         union_4_state_32 x_union_4_state_32;
         union_4_state_33 x_union_4_state_33;
         union_4_state_64 x_union_4_state_64;
         union_4_state_65 x_union_4_state_65;
         union_4_state_128 x_union_4_state_128;

         // Basic types as per IEEE 1800-2017 35.5.6
         x_byte              =  8'd10 -  8'(i); i_byte(x_byte);                            if (x_byte              !==  8'd110 -  8'(i)) $stop;
         x_byte_unsigned     =  8'd20 -  8'(i); i_byte_unsigned(x_byte_unsigned);          if (x_byte_unsigned     !==  8'd220 -  8'(i)) $stop;
         x_shortint          = 16'd30 - 16'(i); i_shortint(x_shortint);                    if (x_shortint          !== 16'd330 - 16'(i)) $stop;
         x_shortint_unsigned = 16'd40 - 16'(i); i_shortint_unsigned(x_shortint_unsigned);  if (x_shortint_unsigned !== 16'd440 - 16'(i)) $stop;
         x_int               = 32'd50 - 32'(i); i_int(x_int);                              if (x_int               !== 32'd550 - 32'(i)) $stop;
         x_int_unsigned      = 32'd60 - 32'(i); i_int_unsigned(x_int_unsigned);            if (x_int_unsigned      !== 32'd660 - 32'(i)) $stop;
         x_longint           = 64'd70 - 64'(i); i_longint(x_longint);                      if (x_longint           !== 64'd770 - 64'(i)) $stop;
         x_longint_unsigned  = 64'd80 - 64'(i); i_longint_unsigned(x_longint_unsigned);    if (x_longint_unsigned  !== 64'd880 - 64'(i)) $stop;
`ifndef NO_TIME
         x_time              = 64'd90 - 64'(i); i_time(x_time);                            if (x_time              !== 64'd990 - 64'(i)) $stop;
`endif
`ifndef NO_INTEGER
         x_integer           = 32'd100- 32'(i); i_integer(x_integer);                      if (x_integer           !== 32'd1100- 32'(i)) $stop;
`endif
         x_real              = -1.0*i - 0.50;   i_real(x_real);                            if (x_real              !=  -100.0 + -1.0*i - 0.50) $stop;
`ifndef NO_SHORTREAL
         x_shortreal         = -1.0*i - 0.25;   i_shortreal(x_shortreal);                  if (x_shortreal         !=  -200.0 + -1.0*i - 0.25) $stop;
`endif
         if (~i[0]) begin
            x_chandle = `NULL;  i_chandle(x_chandle); if (x_chandle !== `NULL) $stop;
            x_string = "Hello"; i_string(x_string);   if (x_string != "Good") $stop;
         end else begin
            x_chandle = `NULL;  i_chandle(x_chandle); if (x_chandle === `NULL) $stop;
            x_string = "World"; i_string(x_string);   if (x_string != "Bye" ) $stop;
         end
         x_bit   = ~i[0]; i_bit(x_bit);     if (x_bit     !==  i[0]) $stop;
         x_logic =  i[0]; i_logic(x_logic); if (x_logic   !== ~i[0]) $stop;

         // Basic types via typedefs
         x_byte_t              =  8'd10 -  8'(2*i); i_byte_t(x_byte_t);                           if (x_byte_t              !==  8'd111 -  8'(2*i)) $stop;
         x_byte_unsigned_t     =  8'd20 -  8'(2*i); i_byte_unsigned_t(x_byte_unsigned_t);         if (x_byte_unsigned_t     !==  8'd222 -  8'(2*i)) $stop;
         x_shortint_t          = 16'd30 - 16'(2*i); i_shortint_t(x_shortint_t);                   if (x_shortint_t          !== 16'd333 - 16'(2*i)) $stop;
         x_shortint_unsigned_t = 16'd40 - 16'(2*i); i_shortint_unsigned_t(x_shortint_unsigned_t); if (x_shortint_unsigned_t !== 16'd444 - 16'(2*i)) $stop;
         x_int_t               = 32'd50 - 32'(2*i); i_int_t(x_int_t);                             if (x_int_t               !== 32'd555 - 32'(2*i)) $stop;
         x_int_unsigned_t      = 32'd60 - 32'(2*i); i_int_unsigned_t(x_int_unsigned_t);           if (x_int_unsigned_t      !== 32'd666 - 32'(2*i)) $stop;
         x_longint_t           = 64'd70 - 64'(2*i); i_longint_t(x_longint_t);                     if (x_longint_t           !== 64'd777 - 64'(2*i)) $stop;
         x_longint_unsigned_t  = 64'd80 - 64'(2*i); i_longint_unsigned_t(x_longint_unsigned_t);   if (x_longint_unsigned_t  !== 64'd888 - 64'(2*i)) $stop;
`ifndef NO_TIME
         x_time_t              = 64'd90 - 64'(2*i); i_time_t(x_time_t);                           if (x_time_t              !== 64'd999 - 64'(2*i)) $stop;
`endif
`ifndef NO_INTEGER
         x_integer_t           = 32'd100- 32'(2*i); i_integer_t(x_integer_t);                     if (x_integer_t           !== 32'd1101- 32'(2*i)) $stop;
`endif
         x_real_t              = -1.0*(2*i) - 0.50; i_real_t(x_real_t);                           if (x_real_t              !=  -111.0 + -1.0*(2*i) - 0.50) $stop;
`ifndef NO_SHORTREAL
         x_shortreal_t         = -1.0*(2*i) - 0.25; i_shortreal_t(x_shortreal_t);                 if (x_shortreal_t         !=  -222.0 + -1.0*(2*i) - 0.25) $stop;
`endif
         if (~i[0]) begin
            x_chandle_t = `NULL;  i_chandle_t(x_chandle_t); if (x_chandle_t === `NULL) $stop;
            x_string_t = "World"; i_string_t(x_string_t);   if (x_string_t != "Bye") $stop;
         end else begin
            x_chandle_t = `NULL;  i_chandle_t(x_chandle_t); if (x_chandle_t !== `NULL) $stop;
            x_string_t = "Hello"; i_string_t(x_string_t);   if (x_string_t != "Good") $stop;
         end
         x_bit_t   = ~i[0]; i_bit_t(x_bit_t);     if (x_bit_t     !==  i[0]) $stop;
         x_logic_t =  i[0]; i_logic_t(x_logic_t); if (x_logic_t   !== ~i[0]) $stop;

         // 2-state packed arrays
         x_bit_1   = ~i[0];        i_array_2_state_1(x_bit_1);     if (x_bit_1   !== i[0]       ) $stop;
         x_bit_32  = ~32'd0 << i;  i_array_2_state_32(x_bit_32);   if (x_bit_32  !== ~32'd0 >> i) $stop;
         x_bit_33  = ~33'd0 << i;  i_array_2_state_33(x_bit_33);   if (x_bit_33  !== ~33'd0 >> i) begin $display("%d %x %0x", i, x_bit_33, ~33'd0 >> i); $stop; end
         x_bit_64  = ~64'd0 << i;  i_array_2_state_64(x_bit_64);   if (x_bit_64  !== ~64'd0 >> i) $stop;
         x_bit_65  = ~65'd0 << i;  i_array_2_state_65(x_bit_65);   if (x_bit_65  !== ~65'd0 >> i) $stop;
         x_bit_128 = ~128'd0<< i;  i_array_2_state_128(x_bit_128); if (x_bit_128 !== ~128'd0>> i) $stop;

         // 2-state packed structures
         x_struct_2_state_1  = ~i[0];        i_struct_2_state_1(x_struct_2_state_1);     if (x_struct_2_state_1  !== i[0]       ) $stop;
         x_struct_2_state_32 = ~32'd0 << i;  i_struct_2_state_32(x_struct_2_state_32);   if (x_struct_2_state_32 !== ~32'd0 >> i) $stop;
         x_struct_2_state_33 = ~33'd0 << i;  i_struct_2_state_33(x_struct_2_state_33);   if (x_struct_2_state_33 !== ~33'd0 >> i) $stop;
         x_struct_2_state_64 = ~64'd0 << i;  i_struct_2_state_64(x_struct_2_state_64);   if (x_struct_2_state_64 !== ~64'd0 >> i) $stop;
         x_struct_2_state_65 = ~65'd0 << i;  i_struct_2_state_65(x_struct_2_state_65);   if (x_struct_2_state_65 !== ~65'd0 >> i) $stop;
         x_struct_2_state_128= ~128'd0<< i;  i_struct_2_state_128(x_struct_2_state_128); if (x_struct_2_state_128!== ~128'd0>> i) $stop;

         // 2-state packed unions
         x_union_2_state_1   = ~i[0];        i_union_2_state_1(x_union_2_state_1);     if (x_union_2_state_1   !== i[0]       ) $stop;
         x_union_2_state_32  = ~32'd0 << i;  i_union_2_state_32(x_union_2_state_32);   if (x_union_2_state_32  !== ~32'd0 >> i) $stop;
         x_union_2_state_33  = ~33'd0 << i;  i_union_2_state_33(x_union_2_state_33);   if (x_union_2_state_33  !== ~33'd0 >> i) $stop;
         x_union_2_state_64  = ~64'd0 << i;  i_union_2_state_64(x_union_2_state_64);   if (x_union_2_state_64  !== ~64'd0 >> i) $stop;
         x_union_2_state_65  = ~65'd0 << i;  i_union_2_state_65(x_union_2_state_65);   if (x_union_2_state_65  !== ~65'd0 >> i) $stop;
         x_union_2_state_128 = ~128'd0<< i;  i_union_2_state_128(x_union_2_state_128); if (x_union_2_state_128 !== ~128'd0>> i) $stop;

         // 4-state packed arrays
         x_logic_1   = ~i[0];        i_array_4_state_1(x_logic_1);     if (x_logic_1   !== i[0]       ) $stop;
         x_logic_32  = ~32'd0 << i;  i_array_4_state_32(x_logic_32);   if (x_logic_32  !== ~32'd0 >> i) $stop;
         x_logic_33  = ~33'd0 << i;  i_array_4_state_33(x_logic_33);   if (x_logic_33  !== ~33'd0 >> i) $stop;
         x_logic_64  = ~64'd0 << i;  i_array_4_state_64(x_logic_64);   if (x_logic_64  !== ~64'd0 >> i) $stop;
         x_logic_65  = ~65'd0 << i;  i_array_4_state_65(x_logic_65);   if (x_logic_65  !== ~65'd0 >> i) $stop;
         x_logic_128 = ~128'd0<< i;  i_array_4_state_128(x_logic_128); if (x_logic_128 !== ~128'd0>> i) $stop;

         // 4-state packed structures
         x_struct_4_state_1  = ~i[0];        i_struct_4_state_1(x_struct_4_state_1);     if (x_struct_4_state_1  !== i[0]       ) $stop;
         x_struct_4_state_32 = ~32'd0 << i;  i_struct_4_state_32(x_struct_4_state_32);   if (x_struct_4_state_32 !== ~32'd0 >> i) $stop;
         x_struct_4_state_33 = ~33'd0 << i;  i_struct_4_state_33(x_struct_4_state_33);   if (x_struct_4_state_33 !== ~33'd0 >> i) $stop;
         x_struct_4_state_64 = ~64'd0 << i;  i_struct_4_state_64(x_struct_4_state_64);   if (x_struct_4_state_64 !== ~64'd0 >> i) $stop;
         x_struct_4_state_65 = ~65'd0 << i;  i_struct_4_state_65(x_struct_4_state_65);   if (x_struct_4_state_65 !== ~65'd0 >> i) $stop;
         x_struct_4_state_128= ~128'd0<< i;  i_struct_4_state_128(x_struct_4_state_128); if (x_struct_4_state_128!== ~128'd0>> i) $stop;

         // 4-state packed unions
         x_union_4_state_1   = ~i[0];        i_union_4_state_1(x_union_4_state_1);     if (x_union_4_state_1   !== i[0]       ) $stop;
         x_union_4_state_32  = ~32'd0 << i;  i_union_4_state_32(x_union_4_state_32);   if (x_union_4_state_32  !== ~32'd0 >> i) $stop;
         x_union_4_state_33  = ~33'd0 << i;  i_union_4_state_33(x_union_4_state_33);   if (x_union_4_state_33  !== ~33'd0 >> i) $stop;
         x_union_4_state_64  = ~64'd0 << i;  i_union_4_state_64(x_union_4_state_64);   if (x_union_4_state_64  !== ~64'd0 >> i) $stop;
         x_union_4_state_65  = ~65'd0 << i;  i_union_4_state_65(x_union_4_state_65);   if (x_union_4_state_65  !== ~65'd0 >> i) $stop;
         x_union_4_state_128 = ~128'd0<< i;  i_union_4_state_128(x_union_4_state_128); if (x_union_4_state_128 !== ~128'd0>> i) $stop;

         // Check the exports
         check_exports();
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
