// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Anthony Donlon.
// SPDX-License-Identifier: CC0-1.0

`define CHECK_TYPE_EQ(gotv, expv) \
    if (gotv != expv) begin $error("%%Error: %s:%0d:  types mismatch\n", `__FILE__, `__LINE__); end
`define CHECK_EQ(gotv, expv) \
    if ((gotv) !== (expv)) begin $error("%%Error: %s:%0d:  got=0x%x exp=0x%x\n", `__FILE__, `__LINE__, (gotv), (expv)); end

class ClsA # (
    parameter int A = 10,
    parameter int B = A + 10,
    parameter int C = B + 10
);
    typedef bit [C-1:0] T;
endclass : ClsA

/* verilator lint_off WIDTHTRUNC */
/* verilator lint_off WIDTHEXPAND */
class ClsAA # (
    parameter             A = 10,
    parameter logic [7:0] B = 8'(A + 10),
    parameter type        C,
    parameter bit [A-1:0] D = A'(B + 10),
    parameter             E = B + 10,
    parameter C           F = 0,
    parameter C           G[$bits(D)] = '{default: 0},
    parameter bit [7:0]   H[A] = '{default: 0}
);
endclass : ClsAA
/* verilator lint_on WIDTHTRUNC */
/* verilator lint_on WIDTHEXPAND */

class ClsB # (
    parameter int  A = 10,
    parameter type B = logic [A-1:0],
    parameter int  C = $bits(B)
);
    typedef bit [C-1:0] T;
endclass : ClsB

class ClsC # (
    parameter int  A = 0,
    parameter type B = logic [A-1:0],
    parameter type C = B,
    parameter type D = C
);
    typedef bit [A-1:0] T1;
    typedef C T2;
    typedef ClsA#(A) T3;
    typedef ClsC#(A, B, C) T4;
    // typedef ClsC#(A, T3, T2, T1) T4;
    // typedef ClsC#(A + 10, T4::T4, T4::T5) T5;
endclass : ClsC

module t;

    /// ClsA #(10, 20, 30)
    ClsA                   a0 = new;
    ClsA #()               a1 = new;
    ClsA #(10)             a2 = new;
    ClsA #(10)             a3 = new; // same overridden
    ClsA #(.B(20))         a4 = new;
    ClsA #(.C(30))         a5 = new;
    ClsA #(.B(20), .C(30)) a6 = new;
    ClsA #(.C(30), .A(10)) a7 = new;
    ClsA #(10, 20, 30)     a8 = new;
    /* verilator lint_off REALCVT */
    ClsA #(10.24, 19.89)   a9 = new;
    /* verilator lint_on REALCVT */

    // TODO: support `CHECK_TYPE_EQ(type(ClsA), type(ClsA#()));
    // TODO: support `CHECK_EQ($typename(a0), $typename(a6));
    initial begin
        a0 = a1;
        a0 = a2;
        a0 = a3;
        a0 = a4;
        a0 = a5;
        a0 = a6;
        a0 = a7;
        a0 = a8;
        a0 = a9;
    end

    parameter PARAM_1 = 4'd10;
    parameter PARAM_2 = 6'd10;

    ClsAA #(10, 257, int) aa10 = new;
    ClsAA #(10, 1, int)   aa11 = new;
    ClsAA #(.A(10), .B(257), .D(11), .C(int))   aa12 = new;

    ClsAA #(.A(7), .B(250),                 .C(int))   aa20 = new;
    ClsAA #(.A(7), .B(120), .D(2),          .C(int))   aa21 = new;
    ClsAA #(.A(7), .B(120),        .E(130), .C(int))   aa22 = new;

    initial begin
        aa10 = aa11;
        aa10 = aa12;
        aa20 = aa21;
        aa20 = aa22;
    end



    /// ClsA #(10, 20, 30)
    ClsB                             b0 = new;
    ClsB #(.B(logic[9:0]))           b1 = new;

    /// ClsA #(20, 20, 30)
    ClsB #(.A(20),.B(logic[19:0]))       b10 = new;
    ClsB #(.A(20),.C(20))                b11 = new;
    ClsB #(.A(20),.B(logic[19:0]), .C(20))   b12 = new;

    ClsB #(.B(logic[19:0]))          b20 = new;
    ClsB #(.B(logic[19:0]), .C(20))  b21 = new;
    ClsB #(.A(10),.B(logic[19:0]), .C(20))   b22 = new;
    // ClsB #(10,.B(bit [$bits(ClsB#()::B)-1:0]), 20)   b23 = new; // TODO: error

    initial begin
        b0 = b1;
        // b0 = b2;
        b10 = b11;
        b10 = b12;
        b20 = b21;
        b20 = b22;
        // b20 = b23;
        // b0 = b3;
        // b0 = b4;
        // b0 = b5;
        // b0 = b6;
        // b0 = b7;
    end

    ClsC #(.A(10), .B(int))   c10 = new;
    ClsC #(.A(10), .B(int), .D(int))   c11 = new;
    ClsC #(.A(10), .B(int), .D(int))   c12 = new;

    ClsC #(.A(10), .B(ClsB))   c20 = new;
    ClsC #(.A(10), .B(ClsB), .D(ClsB#(.B(logic[9:0]), .C(10))))   c21 = new;
    ClsC #(.A(10), .B(ClsB), .C(ClsB#(.A(20 / 2))))   c22 = new;

    parameter type ClsB_20_pt = ClsB #(.B(logic[19:0]));
    typedef ClsB #(.B(logic[19:0])) ClsB_20_t;
    typedef ClsB_20_pt ClsB_20_t2;
    parameter type ClsB_20_pt2 = ClsB_20_t2;

    parameter type ClsB_30_pt = ClsB #(.B(logic[29:0]));

    ClsC #(.A(30), .B(ClsB#(20)), .C(ClsB#(.A(20/2))))    c30 = new;
    ClsC #(.A(30), .B(ClsB_20_pt), .C(ClsB_20_t2), .D(ClsB#(.A(20/2)))) c31 = new;
    ClsC #(.A(30), .B(ClsB_20_pt), .C(ClsB_20_t2))        c32 = new;
    ClsC #(.A(30), .B(ClsB_20_pt2), .D(ClsB_20_pt))       c33 = new;
    ClsC #(.A(30), .B(ClsB_20_pt2), .D(ClsB_20_t2))       c34 = new;

    initial begin
        c10 = c11;
        c10 = c12;
        c20 = c21;
        c20 = c22;
    end

    ClsC #(.A(30), .B(ClsB_20_pt2), .D(ClsB_30_pt))   c40 = new;

endmodule
