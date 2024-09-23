// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2017 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0h exp=%0h\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   int s;
   logic [255:0] n;

   initial begin
      s = $bits('d123);
      `checkd(s, 32);
      s = $bits('h123);
      `checkd(s, 32);
      s = $bits('o123);
      `checkd(s, 32);
      s = $bits('b101);
      `checkd(s, 32);

      // verilator lint_off WIDTHEXPAND

      // Used to warn "Too many digits for 32 bit number"
      //  ... As that number was unsized ('...) it is limited to 32 bits
      // But other simulators don't warn, and language of (IEEE 1800-2023 5.7.1)
      // has been updated to accepting this legal
      n = 'd123456789123456789123456789;
      s = $bits('d123456789123456789123456789);
      `checkh(n, 256'h661efdf2e3b19f7c045f15);
      `checkd(s, 87);

      n = 'h123456789123456789123456789;
      s = $bits('h123456789123456789123456789);
      `checkh(n, 256'h123456789123456789123456789);
      `checkd(s, 108);

      //FIX octal digits in master test, if don't merge this
      n = 'o123456777123456777123456777;
      s = $bits('o123456777123456777123456777);
      `checkh(n, 256'h53977fca72eff94e5dff);
      `checkd(s, 81);

      n = 'b10101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010;
      s = $bits('b10101010101010101010101010101010101010101010101010101010101010101010101010101010101010101010);
      `checkh(n, 256'haaaaaaaaaaaaaaaaaaaaaaa);
      `checkd(s, 92);

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
