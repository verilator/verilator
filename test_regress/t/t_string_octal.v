// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checko(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   string s;
   initial begin
      s = $sformatf("\099 \119 \121"); // Q Q Q
      // $display("%o %o %o %o %o", s[0], s[1], s[2], s[3], s[4]);
      // Results vary by simulator.  Some possibilities:
      // 0 0 0 0 0
      // 40 71 71 40 11
      // 71 71 40 11 071

      s = $sformatf("\088 \108 \110"); // H H H
      // $display("%o %o %o %o %o", s[0], s[1], s[2], s[3], s[4]);
      // Results vary by simulator.  Some possibilities:
      // 0 0 0 0 0
      // 40 70 70 40 10
      // 70 70 40 10 70

      s = $sformatf("\102\3\12."); // B\023\312.
      // $display("%o %o %o %o %o", s[0], s[1], s[2], s[3], s[4]);
      `checko(s[0], 8'o102);
      `checko(s[1], 8'o003);
      `checko(s[2], 8'o012);
      `checko(s[3], 8'o056);

      s = $sformatf("\102.\3.\12\103"); // B.\023.C
      // $display("%o %o %o %o %o", s[0], s[1], s[2], s[3], s[4]);
      `checko(s[0], 8'o102);
      `checko(s[2], 8'o003);
      `checko(s[4], 8'o012);
      `checko(s[5], 8'o103);
      $display("*-* All Finished *-*");
      $finish;
   end
endmodule
