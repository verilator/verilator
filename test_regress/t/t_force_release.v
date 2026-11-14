// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

// Example from IEEE 1800-2023 10.6.2

module t;
  logic a, b, c, d;
  wire e;

  and and1 (e, a, b, c);

  initial begin
    $monitor("%d d=%b,e=%b", $stime, d, e);
    assign d = a & b & c;
    a = 1;
    b = 0;
    c = 1;
    #10;
    force d = (a | b | c);
    force e = (a | b | c);
    `checkh(d, 1);
    `checkh(e, 1);
    #10;
    release d;
    release e;
    #10;
    `checkh(d, 0);
    `checkh(e, 0);

    $finish;
  end

  // Test: force and release of a whole unpacked array from an always block (#9090)
  logic gsr = 1'b0;
  logic [6:0] ff[3];
  always @(gsr)
    if (gsr) force ff = '{default: 0};
    else release ff;
  initial begin
    ff = '{7'h11, 7'h22, 7'h33};
    #1 gsr = 1'b1;
    #1;
    `checkh(ff[0], 7'h0);
    `checkh(ff[2], 7'h0);
    ff[1] = 7'h44;  // Ignored while forced
    #1;
    `checkh(ff[1], 7'h0);
    gsr = 1'b0;
    #1;
    `checkh(ff[1], 7'h0);  // A variable keeps the forced value until next written
    ff[1] = 7'h55;
    #1;
    `checkh(ff[1], 7'h55);
  end

  // Test: a net returns to its driver on release
  logic [14:0] net_src[2];
  wire [14:0] net_arr[2];
  assign net_arr[0] = net_src[0];
  assign net_arr[1] = net_src[1];
  initial begin
    net_src = '{15'h1234, 15'h2345};
    #1;
    force net_arr = '{15'h0abc, 15'h0bcd};
    #1;
    `checkh(net_arr[1], 15'h0bcd);
    net_src[1] = 15'h3456;
    #1;
    `checkh(net_arr[1], 15'h0bcd);
    release net_arr;
    #1;
    `checkh(net_arr[0], 15'h1234);
    `checkh(net_arr[1], 15'h3456);
  end

  // Test: two dimensions with different ranges, forced whole; a row and a slice of nets
  logic [4:0] arr2d[2:1][0:2];
  logic [4:0] row_drv[2][3];
  wire [4:0] row[2][3];
  logic [4:0] slc_drv[4];
  wire [4:0] slc[4];
  logic [4:0] slc_src[2];
  assign row = row_drv;
  assign slc = slc_drv;
  initial begin
    arr2d = '{'{5'h1, 5'h2, 5'h3}, '{5'h4, 5'h5, 5'h6}};
    row_drv = '{'{5'h1, 5'h2, 5'h3}, '{5'h4, 5'h5, 5'h6}};
    slc_drv = '{5'h1, 5'h2, 5'h3, 5'h4};
    slc_src = '{5'h13, 5'h14};
    #1;
    force arr2d = '{default: 5'h1f};
    force row[1] = '{5'ha, 5'hb, 5'hc};
    force slc[1:2] = slc_src;
    #1;
    `checkh(arr2d[2][0], 5'h1f);
    `checkh(arr2d[1][2], 5'h1f);
    `checkh(row[0][0], 5'h1);
    `checkh(row[1][2], 5'hc);
    `checkh(slc[0], 5'h1);
    `checkh(slc[1], 5'h13);
    `checkh(slc[2], 5'h14);
    `checkh(slc[3], 5'h4);
    slc_src[1] = 5'h18;
    row_drv[1][2] = 5'h1e;  // Ignored while forced
    #1;
    `checkh(slc[2], 5'h18);  // A force is continuous
    `checkh(row[1][2], 5'hc);
    release arr2d;
    release row[1];
    release slc[1:2];
    #1;
    `checkh(arr2d[1][2], 5'h1f);  // A variable keeps the forced value until next written
    `checkh(row[1][2], 5'h1e);  // A net returns to its driver
    `checkh(slc[2], 5'h3);
    arr2d[1][2] = 5'h9;
    #1;
    `checkh(arr2d[1][2], 5'h9);
  end

  // Test: above the default --fslice-element-limit of 256
  logic [6:0] big[300];
  initial begin
    big = '{default: 7'h1};
    #1;
    force big = '{default: 7'h2a};
    #1;
    `checkh(big[0], 7'h2a);
    `checkh(big[299], 7'h2a);
    release big;
    big[299] = 7'h5;
    #1;
    `checkh(big[0], 7'h2a);
    `checkh(big[299], 7'h5);
  end

  // Test: a copy of an array of the same type follows it, and opposite directions pair left
  // to right
  typedef logic [6:0] arr_t[2];
  arr_t cpy;
  arr_t cpy_src;
  logic [6:0] rev[1:0];
  initial begin
    cpy = '{7'h1, 7'h2};
    cpy_src = '{7'h3, 7'h4};
    rev = '{7'h1, 7'h2};
    #1;
    force cpy = cpy_src;
    force rev = cpy_src;
    #1;
    `checkh(cpy[0], 7'h3);
    `checkh(rev[1], 7'h3);
    `checkh(rev[0], 7'h4);
    cpy_src[1] = 7'h8;
    #1;
    `checkh(cpy[1], 7'h8);
    `checkh(rev[0], 7'h8);
    release cpy;
    release rev;
    cpy[1] = 7'h9;
    #1;
    `checkh(cpy[1], 7'h9);
  end

  // Test: a net forced by element, released whole
  logic [6:0] elm_drv[2];
  wire [6:0] elm[2];
  assign elm = elm_drv;
  initial begin
    elm_drv = '{7'h1, 7'h2};
    #1;
    force elm[0] = 7'hc;
    force elm[1] = 7'hd;
    #1;
    `checkh(elm[0], 7'hc);
    `checkh(elm[1], 7'hd);
    release elm;
    #1;
    `checkh(elm[0], 7'h1);
    `checkh(elm[1], 7'h2);
  end

  // Test: procedural continuous assign, then deassign
  logic [14:0] pca[2];
  logic [14:0] pca_src[2];
  initial begin
    pca = '{15'h1, 15'h2};
    pca_src = '{15'h3, 15'h4};
    #1;
    assign pca = pca_src;
    #1;
    `checkh(pca[0], 15'h3);
    pca_src[1] = 15'h7fff;
    #1;
    `checkh(pca[1], 15'h7fff);
    deassign pca;
    pca[1] = 15'h9;
    #1;
    `checkh(pca[1], 15'h9);
  end

  // Test: of structs, forced to a struct variable
  typedef struct {
    logic [4:0] a;
    logic [4:0] b;
  } ps_t;
  ps_t sta[2];
  ps_t psv;
  initial begin
    sta = '{'{5'h1, 5'h2}, '{5'h3, 5'h4}};
    psv = '{5'h5, 5'h6};
    #1;
    force sta = '{default: psv};
    #1;
    `checkh(sta[0].a, 5'h5);
    sta[1].b = 5'h9;  // Ignored while forced
    psv.a = 5'h7;
    #1;
    `checkh(sta[1].a, 5'h7);
    `checkh(sta[1].b, 5'h6);
    release sta;
    sta[1].b = 5'h9;
    #1;
    `checkh(sta[1].b, 5'h9);
  end

  // Test: forceable, so also forced externally; two dimensions not from zero
  logic [6:0] fca[2]  /*verilator forceable*/;
  // verilator lint_off ASCRANGE
  logic [6:0] fc2[3:2][1:2]  /*verilator forceable*/;
  // verilator lint_on ASCRANGE
  initial begin
    fca = '{7'h1, 7'h2};
    fc2 = '{'{7'h1, 7'h2}, '{7'h3, 7'h4}};
    #1;
    force fca = '{7'h5, 7'h6};
    force fc2 = '{'{7'h5, 7'h6}, '{7'h7, 7'h8}};
    #1;
    `checkh(fca[1], 7'h6);
    `checkh(fc2[3][1], 7'h5);
    `checkh(fc2[2][2], 7'h8);
    fca[0] = 7'h7;  // Ignored while forced
    fc2[2][1] = 7'h9;  // Ignored while forced
    #1;
    `checkh(fca[0], 7'h5);
    `checkh(fc2[2][1], 7'h7);
    release fca;
    release fc2;
    deassign fca;  // Never assigned: no effect
    #1;
    `checkh(fca[0], 7'h5);  // Keeps the forced value until next written
    `checkh(fc2[3][2], 7'h6);
    fca[1] = 7'h9;
    fc2[2][1] = 7'h9;
    #1;
    `checkh(fca[0], 7'h5);
    `checkh(fca[1], 7'h9);
    `checkh(fc2[2][1], 7'h9);
    `checkh(fc2[2][2], 7'h8);
  end
endmodule
