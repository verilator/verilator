// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2013 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

typedef struct packed {
   logic [1:0] b1;
   logic [1:0] b2;
   logic [1:0] b3;
   logic [1:0] b4;
} t__aa_bbbbbbb_ccccc_dddddd_eee;

typedef struct packed {
   logic [31:0] a;
   union packed {
      logic [7:0] fbyte;
      t__aa_bbbbbbb_ccccc_dddddd_eee pairs;
   } b1;
   logic [23:0] b2;
   logic [7:0] c1;
   logic [23:0] c2;
   logic [31:0] d;
} t__aa_bbbbbbb_ccccc_dddddd;

typedef struct packed {
   logic [31:0] a;
   logic [31:0] b;
   logic [31:0] c;
   logic [31:0] d;
} t__aa_bbbbbbb_ccccc_eee;

typedef union packed {
   t__aa_bbbbbbb_ccccc_dddddd dddddd;
   t__aa_bbbbbbb_ccccc_eee eee;
} t__aa_bbbbbbb_ccccc;


module t (
    input t__aa_bbbbbbb_ccccc xxxxxxx_yyyyy_zzzz,
    output logic [15:0] datao_pre
);
   always_comb datao_pre = { xxxxxxx_yyyyy_zzzz.dddddd.b1.fbyte, xxxxxxx_yyyyy_zzzz.dddddd.c1 };

endmodule
