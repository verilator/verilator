// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2020 by Geza Lore. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t_dpi_result_type_bad;

   // Illegal result types for DPI functions

   //======================================================================
   // Type definitions
   //======================================================================

   // 2-state packed arrays of width > 32
   typedef bit [ 32:0] array_2_state_33_t;
   typedef bit [ 63:0] array_2_state_64_t;
   typedef bit [ 64:0] array_2_state_65_t;
   typedef bit [127:0] array_2_state_128_t;

   // 2-state packed structures of width > 32
   typedef struct      packed { bit [15:0] x; bit [16:0] y; } struct_2_state_33;
   typedef struct      packed { bit [31:0] x; bit [31:0] y; } struct_2_state_64;
   typedef struct      packed { bit [31:0] x; bit [32:0] y; } struct_2_state_65;
   typedef struct      packed { bit [63:0] x; bit [63:0] y; } struct_2_state_128;

   // 2-state packed unions of width > 32
   typedef union       packed { bit [ 32:0] x; bit y; } union_2_state_33;
   typedef union       packed { bit [ 63:0] x; bit y; } union_2_state_64;
   typedef union       packed { bit [ 64:0] x; bit y; } union_2_state_65;
   typedef union       packed { bit [127:0] x; bit y; } union_2_state_128;

   // 4-state packed arrays of any size
   typedef logic [  0:0] array_4_state_1_t;
   typedef logic [  1:0] array_4_state_2_t;
   typedef logic [  7:0] array_4_state_8_t;
   typedef logic [  8:0] array_4_state_9_t;
   typedef logic [ 15:0] array_4_state_16_t;
   typedef logic [ 16:0] array_4_state_17_t;
   typedef logic [ 31:0] array_4_state_32_t;
   typedef logic [ 32:0] array_4_state_33_t;
   typedef logic [ 63:0] array_4_state_64_t;
   typedef logic [ 64:0] array_4_state_65_t;
   typedef logic [127:0] array_4_state_128_t;

   // 4-state packed structures of any size
   typedef struct        packed { logic [ 0:0] x;               } struct_4_state_1;
   typedef struct        packed { logic [ 0:0] x; bit [ 0:0] y; } struct_4_state_2;
   typedef struct        packed { logic [ 3:0] x; bit [ 3:0] y; } struct_4_state_8;
   typedef struct        packed { logic [ 3:0] x; bit [ 4:0] y; } struct_4_state_9;
   typedef struct        packed { logic [ 7:0] x; bit [ 7:0] y; } struct_4_state_16;
   typedef struct        packed { logic [ 7:0] x; bit [ 8:0] y; } struct_4_state_17;
   typedef struct        packed { logic [15:0] x; bit [15:0] y; } struct_4_state_32;
   typedef struct        packed { logic [15:0] x; bit [16:0] y; } struct_4_state_33;
   typedef struct        packed { logic [31:0] x; bit [31:0] y; } struct_4_state_64;
   typedef struct        packed { logic [31:0] x; bit [32:0] y; } struct_4_state_65;
   typedef struct        packed { logic [63:0] x; bit [63:0] y; } struct_4_state_128;

   // 4-state packed unions of any size
   typedef union         packed { logic [  0:0] x; bit y; } union_4_state_1;
   typedef union         packed { logic [  1:0] x; bit y; } union_4_state_2;
   typedef union         packed { logic [  7:0] x; bit y; } union_4_state_8;
   typedef union         packed { logic [  8:0] x; bit y; } union_4_state_9;
   typedef union         packed { logic [ 15:0] x; bit y; } union_4_state_16;
   typedef union         packed { logic [ 16:0] x; bit y; } union_4_state_17;
   typedef union         packed { logic [ 31:0] x; bit y; } union_4_state_32;
   typedef union         packed { logic [ 32:0] x; bit y; } union_4_state_33;
   typedef union         packed { logic [ 63:0] x; bit y; } union_4_state_64;
   typedef union         packed { logic [ 64:0] x; bit y; } union_4_state_65;
   typedef union         packed { logic [127:0] x; bit y; } union_4_state_128;

   //======================================================================
   // Imports
   //======================================================================

   // 2-state packed arrays of width > 32
   import "DPI-C" function bit [ 32:0] i_array_2_state_33();
   import "DPI-C" function bit [ 63:0] i_array_2_state_64();
   import "DPI-C" function bit [ 64:0] i_array_2_state_65();
   import "DPI-C" function bit [127:0] i_array_2_state_128();

   // 2-state packed arrays of width > 32 via typedef
   import "DPI-C" function array_2_state_33_t  i_array_2_state_33_t();
   import "DPI-C" function array_2_state_64_t  i_array_2_state_64_t();
   import "DPI-C" function array_2_state_65_t  i_array_2_state_65_t();
   import "DPI-C" function array_2_state_128_t i_array_2_state_128_t();

   // 2-state packed structures of width > 32
   import "DPI-C" function struct_2_state_33  i_struct_2_state_33();
   import "DPI-C" function struct_2_state_64  i_struct_2_state_64();
   import "DPI-C" function struct_2_state_65  i_struct_2_state_65();
   import "DPI-C" function struct_2_state_128 i_struct_2_state_128();

   // 2-state packed unions of width > 32
   import "DPI-C" function union_2_state_33  i_union_2_state_33();
   import "DPI-C" function union_2_state_64  i_union_2_state_64();
   import "DPI-C" function union_2_state_65  i_union_2_state_65();
   import "DPI-C" function union_2_state_128 i_union_2_state_128();

   // 4-state basic types
   import "DPI-C" function integer i_integer();

   // 4-state packed arrays of any size
   import "DPI-C" function logic [  0:0] i_array_4_state_1();
   import "DPI-C" function logic [  1:0] i_array_4_state_2();
   import "DPI-C" function logic [  7:0] i_array_4_state_8();
   import "DPI-C" function logic [  8:0] i_array_4_state_9();
   import "DPI-C" function logic [ 15:0] i_array_4_state_16();
   import "DPI-C" function logic [ 16:0] i_array_4_state_17();
   import "DPI-C" function logic [ 31:0] i_array_4_state_32();
   import "DPI-C" function logic [ 32:0] i_array_4_state_33();
   import "DPI-C" function logic [ 63:0] i_array_4_state_64();
   import "DPI-C" function logic [ 64:0] i_array_4_state_65();
   import "DPI-C" function logic [127:0] i_array_4_state_128();

   // 4-state packed arrays of any size via typedef
   import "DPI-C" function array_4_state_1_t   i_array_4_state_1_t();
   import "DPI-C" function array_4_state_2_t   i_array_4_state_2_t();
   import "DPI-C" function array_4_state_8_t   i_array_4_state_8_t();
   import "DPI-C" function array_4_state_9_t   i_array_4_state_9_t();
   import "DPI-C" function array_4_state_16_t  i_array_4_state_16_t();
   import "DPI-C" function array_4_state_17_t  i_array_4_state_17_t();
   import "DPI-C" function array_4_state_32_t  i_array_4_state_32_t();
   import "DPI-C" function array_4_state_33_t  i_array_4_state_33_t();
   import "DPI-C" function array_4_state_64_t  i_array_4_state_64_t();
   import "DPI-C" function array_4_state_65_t  i_array_4_state_65_t();
   import "DPI-C" function array_4_state_128_t i_array_4_state_128_t();

   // 4-state packed structures of any size
   import "DPI-C" function struct_4_state_1   i_struct_4_state_1();
   import "DPI-C" function struct_4_state_2   i_struct_4_state_2();
   import "DPI-C" function struct_4_state_8   i_struct_4_state_8();
   import "DPI-C" function struct_4_state_9   i_struct_4_state_9();
   import "DPI-C" function struct_4_state_16  i_struct_4_state_16();
   import "DPI-C" function struct_4_state_17  i_struct_4_state_17();
   import "DPI-C" function struct_4_state_32  i_struct_4_state_32();
   import "DPI-C" function struct_4_state_33  i_struct_4_state_33();
   import "DPI-C" function struct_4_state_64  i_struct_4_state_64();
   import "DPI-C" function struct_4_state_65  i_struct_4_state_65();
   import "DPI-C" function struct_4_state_128 i_struct_4_state_128();

   // 4-state packed unions of any size
   import "DPI-C" function union_4_state_1   i_union_4_state_1();
   import "DPI-C" function union_4_state_2   i_union_4_state_2();
   import "DPI-C" function union_4_state_8   i_union_4_state_8();
   import "DPI-C" function union_4_state_9   i_union_4_state_9();
   import "DPI-C" function union_4_state_16  i_union_4_state_16();
   import "DPI-C" function union_4_state_17  i_union_4_state_17();
   import "DPI-C" function union_4_state_32  i_union_4_state_32();
   import "DPI-C" function union_4_state_33  i_union_4_state_33();
   import "DPI-C" function union_4_state_64  i_union_4_state_64();
   import "DPI-C" function union_4_state_65  i_union_4_state_65();
   import "DPI-C" function union_4_state_128 i_union_4_state_128();

   //======================================================================
   // Exports
   //======================================================================

   // 2-state packed arrays of width > 32
   export "DPI-C" function e_array_2_state_33;
   export "DPI-C" function e_array_2_state_64;
   export "DPI-C" function e_array_2_state_65;
   export "DPI-C" function e_array_2_state_128;

   // 2-state packed arrays of width > 32 via typedef
   export "DPI-C" function e_array_2_state_33_t;
   export "DPI-C" function e_array_2_state_64_t;
   export "DPI-C" function e_array_2_state_65_t;
   export "DPI-C" function e_array_2_state_128_t;

   // 2-state packed structures of width > 32
   export "DPI-C" function e_struct_2_state_33;
   export "DPI-C" function e_struct_2_state_64;
   export "DPI-C" function e_struct_2_state_65;
   export "DPI-C" function e_struct_2_state_128;

   // 2-state packed unions of width > 32
   export "DPI-C" function e_union_2_state_33;
   export "DPI-C" function e_union_2_state_64;
   export "DPI-C" function e_union_2_state_65;
   export "DPI-C" function e_union_2_state_128;

   // 4-state basic types
   export "DPI-C" function e_integer;

   // 4-state packed arrays of any size
   export "DPI-C" function e_array_4_state_1;
   export "DPI-C" function e_array_4_state_2;
   export "DPI-C" function e_array_4_state_8;
   export "DPI-C" function e_array_4_state_9;
   export "DPI-C" function e_array_4_state_16;
   export "DPI-C" function e_array_4_state_17;
   export "DPI-C" function e_array_4_state_32;
   export "DPI-C" function e_array_4_state_33;
   export "DPI-C" function e_array_4_state_64;
   export "DPI-C" function e_array_4_state_65;
   export "DPI-C" function e_array_4_state_128;

   // 4-state packed arrays of any size via typedef
   export "DPI-C" function e_array_4_state_1_t;
   export "DPI-C" function e_array_4_state_2_t;
   export "DPI-C" function e_array_4_state_8_t;
   export "DPI-C" function e_array_4_state_9_t;
   export "DPI-C" function e_array_4_state_16_t;
   export "DPI-C" function e_array_4_state_17_t;
   export "DPI-C" function e_array_4_state_32_t;
   export "DPI-C" function e_array_4_state_33_t;
   export "DPI-C" function e_array_4_state_64_t;
   export "DPI-C" function e_array_4_state_65_t;
   export "DPI-C" function e_array_4_state_128_t;

   // 4-state packed structures of any size
   export "DPI-C" function e_struct_4_state_1;
   export "DPI-C" function e_struct_4_state_2;
   export "DPI-C" function e_struct_4_state_8;
   export "DPI-C" function e_struct_4_state_9;
   export "DPI-C" function e_struct_4_state_16;
   export "DPI-C" function e_struct_4_state_17;
   export "DPI-C" function e_struct_4_state_32;
   export "DPI-C" function e_struct_4_state_33;
   export "DPI-C" function e_struct_4_state_64;
   export "DPI-C" function e_struct_4_state_65;
   export "DPI-C" function e_struct_4_state_128;

   // 4-state packed unions of any size
   export "DPI-C" function e_union_4_state_1;
   export "DPI-C" function e_union_4_state_2;
   export "DPI-C" function e_union_4_state_8;
   export "DPI-C" function e_union_4_state_9;
   export "DPI-C" function e_union_4_state_16;
   export "DPI-C" function e_union_4_state_17;
   export "DPI-C" function e_union_4_state_32;
   export "DPI-C" function e_union_4_state_33;
   export "DPI-C" function e_union_4_state_64;
   export "DPI-C" function e_union_4_state_65;
   export "DPI-C" function e_union_4_state_128;

   //======================================================================
   // Definitions of exported functions
   //======================================================================

   // 2-state packed arrays of width > 32
   function bit [ 32:0] e_array_2_state_33();  return 0; endfunction
   function bit [ 63:0] e_array_2_state_64();  return 0; endfunction
   function bit [ 64:0] e_array_2_state_65();  return 0; endfunction
   function bit [127:0] e_array_2_state_128(); return 0; endfunction

   // 2-state packed arrays of width > 32 via typedef
   function array_2_state_33_t  e_array_2_state_33_t();  return 0; endfunction
   function array_2_state_64_t  e_array_2_state_64_t();  return 0; endfunction
   function array_2_state_65_t  e_array_2_state_65_t();  return 0; endfunction
   function array_2_state_128_t e_array_2_state_128_t(); return 0; endfunction

   // 2-state packed structures of width > 32
   function struct_2_state_33  e_struct_2_state_33();  return 0; endfunction
   function struct_2_state_64  e_struct_2_state_64();  return 0; endfunction
   function struct_2_state_65  e_struct_2_state_65();  return 0; endfunction
   function struct_2_state_128 e_struct_2_state_128(); return 0; endfunction

   // 2-state packed unions of width > 32
   function union_2_state_33  e_union_2_state_33();  return 0; endfunction
   function union_2_state_64  e_union_2_state_64();  return 0; endfunction
   function union_2_state_65  e_union_2_state_65();  return 0; endfunction
   function union_2_state_128 e_union_2_state_128(); return 0; endfunction

   // 4-state basic types
   function integer e_integer(); return 0; endfunction

   // 4-state packed arrays of any size
   function logic [  0:0] e_array_4_state_1();   return 0; endfunction
   function logic [  1:0] e_array_4_state_2();   return 0; endfunction
   function logic [  7:0] e_array_4_state_8();   return 0; endfunction
   function logic [  8:0] e_array_4_state_9();   return 0; endfunction
   function logic [ 15:0] e_array_4_state_16();  return 0; endfunction
   function logic [ 16:0] e_array_4_state_17();  return 0; endfunction
   function logic [ 31:0] e_array_4_state_32();  return 0; endfunction
   function logic [ 32:0] e_array_4_state_33();  return 0; endfunction
   function logic [ 63:0] e_array_4_state_64();  return 0; endfunction
   function logic [ 64:0] e_array_4_state_65();  return 0; endfunction
   function logic [127:0] e_array_4_state_128(); return 0; endfunction

   // 4-state packed arrays of any size via typedef
   function array_4_state_1_t   e_array_4_state_1_t();   return 0; endfunction
   function array_4_state_2_t   e_array_4_state_2_t();   return 0; endfunction
   function array_4_state_8_t   e_array_4_state_8_t();   return 0; endfunction
   function array_4_state_9_t   e_array_4_state_9_t();   return 0; endfunction
   function array_4_state_16_t  e_array_4_state_16_t();  return 0; endfunction
   function array_4_state_17_t  e_array_4_state_17_t();  return 0; endfunction
   function array_4_state_32_t  e_array_4_state_32_t();  return 0; endfunction
   function array_4_state_33_t  e_array_4_state_33_t();  return 0; endfunction
   function array_4_state_64_t  e_array_4_state_64_t();  return 0; endfunction
   function array_4_state_65_t  e_array_4_state_65_t();  return 0; endfunction
   function array_4_state_128_t e_array_4_state_128_t(); return 0; endfunction

   // 4-state packed structures of any size
   function struct_4_state_1   e_struct_4_state_1();   return 0; endfunction
   function struct_4_state_2   e_struct_4_state_2();   return 0; endfunction
   function struct_4_state_8   e_struct_4_state_8();   return 0; endfunction
   function struct_4_state_9   e_struct_4_state_9();   return 0; endfunction
   function struct_4_state_16  e_struct_4_state_16();  return 0; endfunction
   function struct_4_state_17  e_struct_4_state_17();  return 0; endfunction
   function struct_4_state_32  e_struct_4_state_32();  return 0; endfunction
   function struct_4_state_33  e_struct_4_state_33();  return 0; endfunction
   function struct_4_state_64  e_struct_4_state_64();  return 0; endfunction
   function struct_4_state_65  e_struct_4_state_65();  return 0; endfunction
   function struct_4_state_128 e_struct_4_state_128(); return 0; endfunction

   // 4-state packed unions of any size
   function union_4_state_1   e_union_4_state_1();   return 0; endfunction
   function union_4_state_2   e_union_4_state_2();   return 0; endfunction
   function union_4_state_8   e_union_4_state_8();   return 0; endfunction
   function union_4_state_9   e_union_4_state_9();   return 0; endfunction
   function union_4_state_16  e_union_4_state_16();  return 0; endfunction
   function union_4_state_17  e_union_4_state_17();  return 0; endfunction
   function union_4_state_32  e_union_4_state_32();  return 0; endfunction
   function union_4_state_33  e_union_4_state_33();  return 0; endfunction
   function union_4_state_64  e_union_4_state_64();  return 0; endfunction
   function union_4_state_65  e_union_4_state_65();  return 0; endfunction
   function union_4_state_128 e_union_4_state_128(); return 0; endfunction
endmodule
