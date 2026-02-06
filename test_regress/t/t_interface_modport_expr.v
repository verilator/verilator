// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface my_if #(parameter WIDTH = 1);
  logic [WIDTH-1:0] sig_a, sig_b, sig_c, sig_d;
  logic [WIDTH-1:0] sig_e, sig_f;
  // Multiple expressions same direction
  logic [WIDTH-1:0] m1, m2, m3;

  modport mp1(input .a(sig_a), output .b(sig_b));
  modport mp2(input .a(sig_c), output .b(sig_d));
  // Mixed regular and expression items
  modport mp3(input sig_e, output .f(sig_f));
  // Multiple expressions with same direction
  modport mp4(input .in1(m1), input .in2(m2), output .out(m3));
endinterface

module mod1 (
    my_if.mp1 i
);
  assign i.b = i.a;
endmodule

module mod2 (
    my_if.mp2 i
);
  assign i.b = i.a;
endmodule

module mod3 (
    my_if.mp3 i
);
  assign i.f = i.sig_e;  // sig_e is regular, f is expression
endmodule

module mod4 (
    my_if.mp4 i
);
  assign i.out = i.in1 ^ i.in2;
endmodule

module top ();
  my_if #(.WIDTH(8)) myIf ();
  assign myIf.sig_a = 8'h42, myIf.sig_c = 8'hAB;
  assign myIf.sig_e = 8'hCD;
  assign myIf.m1 = 8'hF0, myIf.m2 = 8'h0F;

  mod1 mod1i (myIf.mp1);
  mod2 mod2i (myIf.mp2);
  mod3 mod3i (myIf.mp3);
  mod4 mod4i (myIf.mp4);

  initial begin
    #1;
    `checkh(myIf.sig_b, 8'h42); // mp1: b = a
    `checkh(myIf.sig_d, 8'hAB); // mp2: b = a
    `checkh(myIf.sig_f, 8'hCD); // mp3: f = sig_e
    `checkh(myIf.m3, 8'hFF);    // mp4: out = in1 ^ in2
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
