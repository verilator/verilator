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
  logic sig_a, sig_b, sig_c, sig_d;

  modport mp1(input .a(sig_a), output .b(sig_b));
  modport mp2(input .a(sig_c), output .b(sig_d));
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

module top ();
  my_if myIf ();
  assign myIf.sig_a = 1'b1, myIf.sig_c = 1'b1;

  mod1 mod1Instance (myIf);
  mod2 mod2Instance (myIf);

  initial begin
    #1;
    `checkh(myIf.sig_a, myIf.sig_b);
    `checkh(myIf.sig_c, myIf.sig_d);
    #1;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
