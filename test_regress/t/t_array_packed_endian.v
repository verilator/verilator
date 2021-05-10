// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

typedef struct packed {
   logic [7:0] a;
} tb_t;

typedef struct packed {
   // verilator lint_off LITENDIAN
   logic [0:7] a;
   // verilator lint_on LITENDIAN
} tl_t;

typedef struct packed {
   logic [7:0] bb;
   // verilator lint_off LITENDIAN
   tb_t [0:1] cbl;
   tb_t [1:0] cbb;
   tl_t [0:1] cll;
   tl_t [1:0] clb;
   logic [0:7] dl;
   // verilator lint_on LITENDIAN
} t2;

logic [2:0][31:0] test2l;
// verilator lint_off LITENDIAN
logic [0:2][31:0] test2b;
logic [0:2][31:0] test1b;
// verilator lint_on LITENDIAN
logic [2:0][31:0] test1l;

module t;
   t2 t;
   initial begin
      t = 80'hcd_1f2f3f4f_5f6f7f8f_c2;
      `checkh(t.bb, 8'hcd);
      `checkh(t.cbl[0].a, 8'h1f);
      `checkh(t.cbl[1].a, 8'h2f);
      `checkh(t.cbb[0].a, 8'h4f);
      `checkh(t.cbb[1].a, 8'h3f);
      `checkh(t.cll[0].a, 8'h5f);
      `checkh(t.cll[1].a, 8'h6f);
      `checkh(t.clb[0].a, 8'h8f);
      `checkh(t.clb[1].a, 8'h7f);
      `checkh(t.dl, 8'hc2);

      t = '0;
      t.bb = 8'h13;
      t.cbl[0].a = 8'hac;
      t.cbl[1].a = 8'had;
      t.cbb[0].a = 8'hae;
      t.cbb[1].a = 8'haf;
      t.cll[0].a = 8'hbc;
      t.cll[1].a = 8'hbd;
      t.clb[0].a = 8'hbe;
      t.clb[1].a = 8'hbf;
      t.dl = 8'h31;
      `checkh(t, 80'h13_acadafae_bcbdbfbe_31);

      t = '0;
      t.bb[7] = 1'b1;
      t.cbl[1].a[1] = 1'b1;
      t.cbb[1].a[2] = 1'b1;
      t.cll[1].a[3] = 1'b1;
      t.clb[1].a[4] = 1'b1;
      t.dl[7] = 1'b1;
      `checkh(t, 80'h80_0002040000100800_01);

      test1b = '{0, 1, 2};
      test1l = test1b;
      test2l = '{2, 1, 0};
      test2b = test2l;
      `checkh(test2l[0], 0);
      `checkh(test2l[2], 2);
      `checkh(test2l, {32'h2, 32'h1, 32'h0});
      `checkh(test2b[0], 2);
      `checkh(test2b[2], 0);
      `checkh(test2b, {32'h2, 32'h1, 32'h0});
      `checkh(test1b[0], 0);
      `checkh(test1b[2], 2);
      `checkh(test1b, {32'h0, 32'h1, 32'h2});
      `checkh(test1l[0], 2);
      `checkh(test1l[2], 0);
      `checkh(test1l, {32'h0, 32'h1, 32'h2});

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
