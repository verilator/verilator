// DESCRIPTION: Verilator: Verilog Test module for specialized type default values
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Mostafa Gamal
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  typedef struct {  // IEEE 1800-2023 5.10
    int a;
    shortint b;
  } ab_struct;

  typedef struct {  // IEEE 1800-2023 10.9.2
    int x;
    int y;
  } st_struct;

  typedef struct {  // IEEE 1800-2023 10.9.2
    int A;
    struct {int B, C;} BC1, BC2;
  } DEF_struct;


  typedef struct {  // IEEE 1800-2023 10.9.2
    int A;
    struct {
      int B, C;
      struct {
        int D, E;
        struct {
          int F;
          shortint G;
        } FG1;
      } DE1;
    } BC1;
  } HIJ_struct;

  ab_struct ab;
  ab_struct abkey[1:0];
  st_struct st;
  int k = 1;
  DEF_struct DEF;
  HIJ_struct HIJ;

  initial begin
    // struct ab
    ab = '{0, 0};  //constant member by position
    `checkd(ab.a, 0);
    `checkd(ab.b, 0);


    ab = '{default: 0};  //default value
    `checkd(ab.a, 0);
    `checkd(ab.b, 0);


    ab = '{int : 1, shortint : 0};  //data type and default value
    `checkd(ab.a, 1);
    `checkd(ab.b, 0);


    abkey[1:0] = '{'{a: 1, b: 2}, '{int : 2, shortint : 3}};  // member: value & data_type: value
    `checkd(abkey[1].a, 1);
    `checkd(abkey[1].b, 2);
    `checkd(abkey[0].a, 2);
    `checkd(abkey[0].b, 3);


    // struct st
    st = '{1, 2 + k};  //constant member by position
    `checkd(st.x, 1);
    `checkd(st.y, 2 + k);

    st = '{x: 2, y: 3 + k};  //member: value
    `checkd(st.x, 2);
    `checkd(st.y, 3 + k);

    st = '{int : 2, int : 3 + k};  //data_type: value override
    `checkd(st.x, 3 + k);
    `checkd(st.y, 3 + k);


    // struct DEF
    DEF = '{A: 1, BC1: '{B: 2, C: 3}, BC2: '{B: 4, C: 5}};
    `checkd(DEF.A, 1);
    `checkd(DEF.BC1.B, 2);
    `checkd(DEF.BC1.C, 3);
    `checkd(DEF.BC2.B, 4);
    `checkd(DEF.BC2.C, 5);


    DEF = '{int : 0, BC1: '{int : 10}, BC2: '{default: 5}};
    `checkd(DEF.A, 0);
    `checkd(DEF.BC1.B, 10);
    `checkd(DEF.BC1.C, 10);
    `checkd(DEF.BC2.B, 5);
    `checkd(DEF.BC2.C, 5);

    DEF = '{default: 1, BC1: '{int : 10}, BC2: '{default: 5}};
    `checkd(DEF.A, 1);
    `checkd(DEF.BC1.B, 10);
    `checkd(DEF.BC1.C, 10);
    `checkd(DEF.BC2.B, 5);
    `checkd(DEF.BC2.C, 5);

    DEF = '{default: 10};
    `checkd(DEF.A, 10);
    `checkd(DEF.BC1.B, 10);
    `checkd(DEF.BC1.C, 10);
    `checkd(DEF.BC2.B, 10);
    `checkd(DEF.BC2.C, 10);

    // struct HIJ
    HIJ = '{int : 10, default: 5};
    `checkd(HIJ.A, 10);
    `checkd(HIJ.BC1.B, 10);
    `checkd(HIJ.BC1.C, 10);
    `checkd(HIJ.BC1.DE1.D, 10);
    `checkd(HIJ.BC1.DE1.E, 10);
    `checkd(HIJ.BC1.DE1.FG1.F, 10);
    `checkd(HIJ.BC1.DE1.FG1.G, 5);

    HIJ = '{shortint : 10, default: 5};
    `checkd(HIJ.A, 5);
    `checkd(HIJ.BC1.B, 5);
    `checkd(HIJ.BC1.C, 5);
    `checkd(HIJ.BC1.DE1.D, 5);
    `checkd(HIJ.BC1.DE1.E, 5);
    `checkd(HIJ.BC1.DE1.FG1.F, 5);
    `checkd(HIJ.BC1.DE1.FG1.G, 10);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
