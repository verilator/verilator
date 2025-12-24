// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

interface my_if;
  logic [15:0] a;
  logic [7:0] b, c;

  modport mp1(input .in(a[7:0]), output .out(b));
  modport mp2(input .in(a[15:8]), output .out(c));
endinterface

module mod1 (
    my_if.mp1 i
);
  assign i.out = i.in;
endmodule

module mod2 (
    my_if.mp2 i
);
  assign i.out = ~i.in;
endmodule

module top ();
  my_if myIf ();
  assign myIf.a = 16'habcd;

  mod1 mod1Instance (myIf);
  mod2 mod2Instance (myIf);

  initial begin
    #1;
    `checkh(myIf.b, myIf.a[7:0]);
    `checkh(myIf.c, ~myIf.a[15:8]);
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
