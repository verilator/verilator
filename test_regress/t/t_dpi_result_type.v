// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

`ifdef VCS
 `define NO_REAL_EXPORT
`endif

`ifdef NC
 `define NO_STRUCT_OR_UNION
 `define NO_SHORTREAL
`endif

`ifdef MS
 `define NO_STRUCT_OR_UNION
 `define NO_ARRAY
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

   // Legal result types for DPI functions

   //======================================================================
   // Type definitions
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.5
   typedef byte byte_t;
   typedef byte unsigned byte_unsigned_t;
   typedef shortint      shortint_t;
   typedef shortint unsigned shortint_unsigned_t;
   typedef int               int_t;
   typedef int unsigned      int_unsigned_t;
   typedef longint           longint_t;
   typedef longint unsigned  longint_unsigned_t;
   typedef real              real_t;
`ifndef NO_SHORTREAL
   typedef shortreal         shortreal_t;
`endif
   typedef chandle           chandle_t;
   typedef string            string_t;
   typedef bit               bit_t;
   typedef logic             logic_t;

   // 2-state packed structures of width <= 32
   typedef struct            packed { bit x; }                      struct_2_state_1;
   typedef struct            packed { bit [15:0] x; bit [15:0] y; } struct_2_state_32;

   // 2-state packed unions of width <= 32
   typedef union             packed { bit x; bit y; }                union_2_state_1;
   typedef union             packed { bit [31:0] x; bit [31:0] y; }  union_2_state_32;

   //======================================================================
   // Imports
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.5
   import "DPI-C" function void              i_void              ();
   import "DPI-C" function byte              i_byte              ();
   import "DPI-C" function byte unsigned     i_byte_unsigned     ();
   import "DPI-C" function shortint          i_shortint          ();
   import "DPI-C" function shortint unsigned i_shortint_unsigned ();
   import "DPI-C" function int               i_int               ();
   import "DPI-C" function int unsigned      i_int_unsigned      ();
   import "DPI-C" function longint           i_longint           ();
   import "DPI-C" function longint unsigned  i_longint_unsigned  ();
   import "DPI-C" function real              i_real              ();
`ifndef NO_SHORTREAL
   import "DPI-C" function shortreal         i_shortreal         ();
`endif
   import "DPI-C" function chandle           i_chandle           ();
   import "DPI-C" function string            i_string            ();
   import "DPI-C" function bit               i_bit               ();
   import "DPI-C" function logic             i_logic             ();

   // Basic types via typedef
   import "DPI-C" function byte_t              i_byte_t              ();
   import "DPI-C" function byte_unsigned_t     i_byte_unsigned_t     ();
   import "DPI-C" function shortint_t          i_shortint_t          ();
   import "DPI-C" function shortint_unsigned_t i_shortint_unsigned_t ();
   import "DPI-C" function int_t               i_int_t               ();
   import "DPI-C" function int_unsigned_t      i_int_unsigned_t      ();
   import "DPI-C" function longint_t           i_longint_t           ();
   import "DPI-C" function longint_unsigned_t  i_longint_unsigned_t  ();
   import "DPI-C" function real_t              i_real_t              ();
`ifndef NO_SHORTREAL
   import "DPI-C" function shortreal_t         i_shortreal_t         ();
`endif
   import "DPI-C" function chandle_t           i_chandle_t           ();
   import "DPI-C" function string_t            i_string_t            ();
   import "DPI-C" function bit_t               i_bit_t               ();
   import "DPI-C" function logic_t             i_logic_t             ();

`ifndef NO_ARRAY
   // 2-state packed arrays of width <= 32
   import "DPI-C" function bit [ 0:0] i_array_2_state_1  ();
   import "DPI-C" function bit [31:0] i_array_2_state_32 ();
`endif

`ifndef NO_STRUCT_OR_UNION
   // 2-state packed structures of width <= 32
   import "DPI-C" function struct_2_state_1   i_struct_2_state_1 ();
   import "DPI-C" function struct_2_state_32  i_struct_2_state_32();

   // 2-state packed unions of width <= 32
   import "DPI-C" function union_2_state_1   i_union_2_state_1 ();
   import "DPI-C" function union_2_state_32  i_union_2_state_32();
`endif

   //======================================================================
   // Exports
   //======================================================================

   // Basic types as per IEEE 1800-2017 35.5.5
   export "DPI-C" function e_void;
   export "DPI-C" function e_byte;
   export "DPI-C" function e_byte_unsigned;
   export "DPI-C" function e_shortint;
   export "DPI-C" function e_shortint_unsigned;
   export "DPI-C" function e_int;
   export "DPI-C" function e_int_unsigned;
   export "DPI-C" function e_longint;
   export "DPI-C" function e_longint_unsigned;
`ifndef NO_REAL_EXPORT
   export "DPI-C" function e_real;
`endif
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
`ifndef NO_REAL_EXPORT
   export "DPI-C" function e_real_t;
`endif
`ifndef NO_SHORTREAL
   export "DPI-C" function e_shortreal_t;
`endif
   export "DPI-C" function e_chandle_t;
   export "DPI-C" function e_string_t;
   export "DPI-C" function e_bit_t;
   export "DPI-C" function e_logic_t;

`ifndef NO_ARRAY
   // 2-state packed arrays of width <= 32
   export "DPI-C" function e_array_2_state_1;
   export "DPI-C" function e_array_2_state_32;
`endif

`ifndef NO_STRUCT_OR_UNION
   // 2-state packed structures of width <= 32
   export "DPI-C" function e_struct_2_state_1;
   export "DPI-C" function e_struct_2_state_32;

   // 2-state packed unions of width <= 32
   export "DPI-C" function e_union_2_state_1;
   export "DPI-C" function e_union_2_state_32;
`endif

   //======================================================================
   // Definitions of exported functions
   //======================================================================

   // Static variables (Note: Verilator strangely assumes everything inside
   // a function is automatic, which is exactly the opposite of the standard
   // see IEEE 1800-2017 13.3.1 and 13.4.2

   // Basic types as per IEEE 1800-2017 35.5.5
   int                       n_void = 0;
   function void e_void();
      $display("e_void %1d", n_void);
      n_void++;
   endfunction

   byte                      n_byte = 0;
   function byte e_byte();
      e_byte = 8'd10 + n_byte;
      n_byte++;
   endfunction

   byte                      n_byte_unsigned = 0;
   function byte unsigned e_byte_unsigned();
      e_byte_unsigned = 8'd20 + n_byte_unsigned;
      n_byte_unsigned++;
   endfunction

   shortint                  n_shortint = 0;
   function shortint e_shortint();
      e_shortint = 16'd30 + n_shortint;
      n_shortint++;
   endfunction

   shortint                  n_shortint_unsigned = 0;
   function shortint unsigned e_shortint_unsigned();
      e_shortint_unsigned = 16'd40 + n_shortint_unsigned;
      n_shortint_unsigned++;
   endfunction

   int                       n_int = 0;
   function int e_int();
      e_int = 32'd50 + n_int;
      n_int++;
   endfunction

   int                       n_int_unsigned = 0;
   function int unsigned e_int_unsigned();
      e_int_unsigned = 32'd60 + n_int_unsigned;
      n_int_unsigned++;
   endfunction

   longint                   n_longint = 0;
   function longint e_longint();
      e_longint = 64'd70 + n_longint;
      n_longint++;
   endfunction

   longint                   n_longint_unsigned = 0;
   function longint unsigned e_longint_unsigned();
      e_longint_unsigned = 64'd80 + n_longint_unsigned;
      n_longint_unsigned++;
   endfunction

`ifndef NO_REAL_EXPORT
   int                       n_real = 0;
   function real e_real();
      e_real = real'(2*n_real + 1) / 2.0;
      n_real++;
   endfunction
`endif

`ifndef NO_SHORTREAL
   int                       n_shortreal = 0;
   function shortreal e_shortreal();
      e_shortreal = shortreal'(4*n_shortreal + 1)/ 4.0;
      n_shortreal++;
   endfunction
`endif

   int                       n_chandle = 0;
   function chandle e_chandle();
      $display("e_chandle %1d", n_chandle);
      e_chandle = `NULL;
      n_chandle++;
   endfunction

   int                       n_string = 0;
   function string e_string();
      $display("e_string %1d", n_string);
      e_string = n_string[0] ? "World" : "Hello";
      n_string++;
   endfunction

   int                       n_bit = 0;
   function bit e_bit();
      $display("e_bit %1d", n_bit);
      e_bit = n_bit[0];
      n_bit++;
   endfunction

   int                       n_logic = 0;
   function logic e_logic();
      $display("e_logic %1d", n_logic);
      e_logic = ~n_logic[0];
      n_logic++;
   endfunction

   // Basic types via typedefs
   byte_t n_byte_t = 0;
   function byte_t e_byte_t();
      e_byte_t = 8'd10 + n_byte_t;
      n_byte_t += 2;
   endfunction

   byte                      n_byte_unsigned_t = 0;
   function byte_unsigned_t e_byte_unsigned_t();
      e_byte_unsigned_t = 8'd20 + n_byte_unsigned_t;
      n_byte_unsigned_t += 2;
   endfunction

   shortint_t n_shortint_t = 0;
   function shortint_t e_shortint_t();
      e_shortint_t = 16'd30 + n_shortint_t;
      n_shortint_t += 2;
   endfunction

   shortint                  n_shortint_unsigned_t = 0;
   function shortint_unsigned_t e_shortint_unsigned_t();
      e_shortint_unsigned_t = 16'd40 + n_shortint_unsigned_t;
      n_shortint_unsigned_t += 2;
   endfunction

   int_t n_int_t = 0;
   function int_t e_int_t();
      e_int_t = 32'd50 + n_int_t;
      n_int_t += 2;
   endfunction

   int                       n_int_unsigned_t = 0;
   function int_unsigned_t e_int_unsigned_t();
      e_int_unsigned_t = 32'd60 + n_int_unsigned_t;
      n_int_unsigned_t += 2;
   endfunction

   longint_t n_longint_t = 0;
   function longint_t e_longint_t();
      e_longint_t = 64'd70 + n_longint_t;
      n_longint_t += 2;
   endfunction

   longint                   n_longint_unsigned_t = 0;
   function longint_unsigned_t e_longint_unsigned_t();
      e_longint_unsigned_t = 64'd80 + n_longint_unsigned_t;
      n_longint_unsigned_t += 2;
   endfunction

`ifndef NO_REAL_EXPORT
   int                       n_real_t = 0;
   function real_t e_real_t();
      e_real_t = real'(2*n_real_t + 1) / 2.0;
      n_real_t += 2;
   endfunction
`endif

`ifndef NO_SHORTREAL
   int                       n_shortreal_t = 0;
   function shortreal_t e_shortreal_t();
      e_shortreal_t = shortreal'(4*n_shortreal_t + 1)/ 4.0;
      n_shortreal_t += 2;
   endfunction
`endif

   int                       n_chandle_t = 0;
   function chandle_t e_chandle_t();
      $display("e_chandle_t %1d", n_chandle_t);
      e_chandle_t = `NULL;
      n_chandle_t++;
   endfunction

   int                       n_string_t = 0;
   function string_t e_string_t();
      $display("e_string_t %1d", n_string_t);
      e_string_t = n_string_t[0] ? "World" : "Hello";
      n_string_t++;
   endfunction

   int                       n_bit_t = 0;
   function bit_t e_bit_t();
      $display("e_bit_t %1d", n_bit_t);
      e_bit_t = n_bit_t[0];
      n_bit_t++;
   endfunction

   int                       n_logic_t = 0;
   function logic_t e_logic_t();
      $display("e_logic_t %1d", n_logic_t);
      e_logic_t = ~n_logic_t[0];
      n_logic_t++;
   endfunction

`ifndef NO_ARRAY
   // 2-state packed arrays of width <= 32
   int                       n_array_2_state_1 = 0;
   function bit [ 0:0] e_array_2_state_1();
      $display("e_array_2_state_1 %1d", n_array_2_state_1);
      e_array_2_state_1 = n_array_2_state_1[0];
      n_array_2_state_1++;
   endfunction

   int                       n_array_2_state_32 = 0;
   function bit [31:0] e_array_2_state_32();
      $display("e_array_2_state_32 %1d", n_array_2_state_32);
      e_array_2_state_32 = ~32'd0 >> n_array_2_state_32;
      n_array_2_state_32++;
   endfunction
`endif

`ifndef NO_STRUCT_OR_UNION
   // 2-state packed structures of width <= 32
   int                       n_struct_2_state_1 = 0;
   function struct_2_state_1 e_struct_2_state_1();
      $display("e_struct_2_state_1 %1d",  n_struct_2_state_1);
      e_struct_2_state_1 = n_struct_2_state_1[0];
      n_struct_2_state_1++;
   endfunction

   int                       n_struct_2_state_32 = 0;
   function struct_2_state_32  e_struct_2_state_32();
      $display("e_struct_2_state_32 %1d", n_struct_2_state_32);
      e_struct_2_state_32 = ~32'd0 >> n_struct_2_state_32;
      n_struct_2_state_32++;
   endfunction

   // 2-state packed unions of width <= 32
   int                       n_union_2_state_1 = 0;
   function union_2_state_1 e_union_2_state_1();
      $display("e_union_2_state_1 %1d", n_union_2_state_1);
      e_union_2_state_1 = n_union_2_state_1[0];
      n_union_2_state_1++;
   endfunction

   int                       n_union_2_state_32 = 0;
   function union_2_state_32 e_union_2_state_32();
      $display("e_union_2_state_32 %1d", n_union_2_state_32);
      e_union_2_state_32 = ~32'd0 >> n_union_2_state_32;
      n_union_2_state_32++;
   endfunction
`endif

   //======================================================================
   // Invoke all functions 3 times (they have side effects)
   //======================================================================

   import "DPI-C" context function void check_exports();

   initial begin
      for (int i = 0 ; i < 3; i++) begin
         // Check the imports

         // Basic types as per IEEE 1800-2017 35.5.5
         i_void();
         if (i_byte()              !==  8'd10 -  8'(i)) $stop;
         if (i_byte_unsigned()     !==  8'd20 -  8'(i)) $stop;
         if (i_shortint()          !== 16'd30 - 16'(i)) $stop;
         if (i_shortint_unsigned() !== 16'd40 - 16'(i)) $stop;
         if (i_int()               !== 32'd50 - 32'(i)) $stop;
         if (i_int_unsigned()      !== 32'd60 - 32'(i)) $stop;
         if (i_longint()           !== 64'd70 - 64'(i)) $stop;
         if (i_longint_unsigned()  !== 64'd80 - 64'(i)) $stop;
         if (i_real()              !=  -1.0*i - 0.5 ) $stop;
`ifndef NO_SHORTREAL
         if (i_shortreal()         !=  -1.0*i - 0.25) $stop;
`endif
         if (~i[0]) begin
            if (i_chandle() !== `NULL) $stop;
            if (i_string() != "World") $stop;
         end else begin
            if (i_chandle() === `NULL) $stop;
            if (i_string() != "Hello") $stop;
         end
         if (i_bit()     !== ~i[0]) $stop;
         if (i_logic()   !==  i[0]) $stop;

         // Basic types via typedefs
         if (i_byte_t()              !==  8'd10 -  8'(2*i)) $stop;
         if (i_byte_unsigned_t()     !==  8'd20 -  8'(2*i)) $stop;
         if (i_shortint_t()          !== 16'd30 - 16'(2*i)) $stop;
         if (i_shortint_unsigned_t() !== 16'd40 - 16'(2*i)) $stop;
         if (i_int_t()               !== 32'd50 - 32'(2*i)) $stop;
         if (i_int_unsigned_t()      !== 32'd60 - 32'(2*i)) $stop;
         if (i_longint_t()           !== 64'd70 - 64'(2*i)) $stop;
         if (i_longint_unsigned_t()  !== 64'd80 - 64'(2*i)) $stop;
         if (i_real_t()              !=  -1.0*(2*i) - 0.5 ) $stop;
`ifndef NO_SHORTREAL
         if (i_shortreal_t()         !=  -1.0*(2*i) - 0.25) $stop;
`endif
         if (~i[0]) begin
            if (i_chandle_t() !== `NULL) $stop;
            if (i_string_t() != "World") $stop;
         end else begin
            if (i_chandle_t() === `NULL) $stop;
            if (i_string_t() != "Hello") $stop;
         end
         if (i_bit_t()     !== ~i[0]) $stop;
         if (i_logic_t()   !==  i[0]) $stop;

`ifndef NO_ARRAY
         // 2-state packed arrays of width <= 32
         if (i_array_2_state_1()   !== ~i[0]      ) $stop;
         if (i_array_2_state_32()  !== ~32'd0 << i) $stop;
`endif

`ifndef NO_STRUCT_OR_UNION
         // 2-state packed structures of width <= 32
         if (i_struct_2_state_1()  !== ~i[0]      ) $stop;
         if (i_struct_2_state_32() !== ~32'd0 << i) $stop;

         // 2-state packed unions of width <= 32
         if (i_union_2_state_1()   !== ~i[0]      ) $stop;
         if (i_union_2_state_32()  !== ~32'd0 << i) $stop;
`endif

         // Check the exports
         check_exports();
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
