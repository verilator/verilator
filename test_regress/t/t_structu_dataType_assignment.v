// DESCRIPTION: Verilator: Verilog Test module for specialized type default values
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Mostafa Gamal.
// SPDX-License-Identifier: CC0-1.0

/* verilator lint_off UNPACKED */

module top();

  typedef struct { // IEEE 1800-2017 SV CH:5.10
    int a;
    shortint b;
  } ab_struct;

  typedef struct { // IEEE 1800-2017 SV CH:10.9.2
  int x;
  int y;
  } st_struct;

  typedef struct { // IEEE 1800-2017 SV CH:10.9.2
    logic [7:0] a;
    bit b;
    bit signed [31:0] c;
    int s;
  } sa_struct;


  typedef struct { // IEEE 1800-2017 SV CH:10.9.2
    int A;
    struct {
    int B, C;
    } BC1, BC2;
  } DEF_struct;


  typedef struct { // IEEE 1800-2017 SV CH:10.9.2
    int A;
    struct {
      int B, C;
      struct{
        int D, E;
        struct{
          int F;
          shortint G;
        } FG1;
      } DE1;
    } BC1;
  } HIJ_struct;

  // struct ab
  ab_struct ab;
  ab_struct abkey[1:0];

  // struct st
  st_struct st;
  int k = 1;

  // struct sa
  sa_struct sa;

  // struct DEF
  DEF_struct DEF;

  // struct HIJ
  HIJ_struct HIJ;

  initial begin;
   // struct ab
   ab = '{0, 0}; //constant member by position
   if (ab.a != 0) $stop;
   if (ab.b != 0) $stop;


   ab = '{default: 0}; //default value
   if (ab.a != 0) $stop;
   if (ab.b != 0) $stop;


   ab = '{int: 1, shortint: 0}; //data type and default value
   if (ab.a != 1) $stop;
   if (ab.b != 0) $stop;


   abkey[1:0] = '{'{a:1, b:2}, '{int:2, shortint:3}}; // member: value & data_type: value
   if (abkey[1].a != 1) $stop;
   if (abkey[1].b != 2) $stop;
   if (abkey[0].a != 2) $stop;
   if (abkey[0].b != 3) $stop;


   // struct st
   st = '{1, 2+k}; //constant member by position
   if (st.x != 1) $stop;
   if (st.y != 2+k) $stop;

   st = '{x:2, y:3+k}; //member: value
   if (st.x != 2) $stop;
   if (st.y != 3+k) $stop;

   st = '{int:2, int:3+k}; //data_type: value override
   if (st.x != 3+k) $stop;
   if (st.y != 3+k) $stop;


   // struct sa
   sa = '{default:'1};
   if (sa.a != '1) $stop;
   if (sa.b != '1) $stop;
   if (sa.c != '1) $stop;
   if (sa.s != '1) $stop;

   sa = '{default:'1, int: 5};
   if (sa.a != '1) $stop;
   if (sa.b != '1) $stop;
   if (sa.c != '1) $stop;
   if (sa.s != 5) $stop;


   sa = '{default:'1, int: 5, b: 0};
   if (sa.a != '1) $stop;
   if (sa.b != 0) $stop;
   if (sa.c != '1) $stop;
   if (sa.s != 5) $stop;


   // struct DEF
   DEF = '{A:1, BC1:'{B:2, C:3}, BC2:'{B:4,C:5}};
   if (DEF.A != 1) $stop;
   if (DEF.BC1.B != 2) $stop;
   if (DEF.BC1.C != 3) $stop;
   if (DEF.BC2.B != 4) $stop;
   if (DEF.BC2.C != 5) $stop;


   DEF = '{int:0, BC1:'{int:10}, BC2:'{default:5}};
   if (DEF.A != 0) $stop;
   if (DEF.BC1.B != 10) $stop;
   if (DEF.BC1.C != 10) $stop;
   if (DEF.BC2.B != 5) $stop;
   if (DEF.BC2.C != 5) $stop;

   DEF = '{default:1, BC1:'{int:10}, BC2:'{default:5}};
   if (DEF.A != 1) $stop;
   if (DEF.BC1.B != 10) $stop;
   if (DEF.BC1.C != 10) $stop;
   if (DEF.BC2.B != 5) $stop;
   if (DEF.BC2.C != 5) $stop;

   DEF = '{default:10};
   if (DEF.A != 10) $stop;
   if (DEF.BC1.B != 10) $stop;
   if (DEF.BC1.C != 10) $stop;
   if (DEF.BC2.B != 10) $stop;
   if (DEF.BC2.C != 10) $stop;

   DEF = '{int:10};
   if (DEF.A != 10) $stop;
   if (DEF.BC1.B != 10) $stop;
   if (DEF.BC1.C != 10) $stop;
   if (DEF.BC2.B != 10) $stop;
   if (DEF.BC2.C != 10) $stop;

   // struct HIJ
   HIJ = '{int:10, default: 5};
   if (HIJ.A != 10) $stop;
   if (HIJ.BC1.B != 10) $stop;
   if (HIJ.BC1.C != 10) $stop;
   if (HIJ.BC1.DE1.D != 10) $stop;
   if (HIJ.BC1.DE1.E != 10) $stop;
   if (HIJ.BC1.DE1.FG1.F != 10) $stop;
   if (HIJ.BC1.DE1.FG1.G != 5) $stop;

   HIJ = '{shortint:10, default: 5};
   if (HIJ.A != 5) $stop;
   if (HIJ.BC1.B != 5) $stop;
   if (HIJ.BC1.C != 5) $stop;
   if (HIJ.BC1.DE1.D != 5) $stop;
   if (HIJ.BC1.DE1.E != 5) $stop;
   if (HIJ.BC1.DE1.FG1.F != 5) $stop;
   if (HIJ.BC1.DE1.FG1.G != 10) $stop;

   $write("*-* All Finished *-*\n");
   $finish;
  end

endmodule
