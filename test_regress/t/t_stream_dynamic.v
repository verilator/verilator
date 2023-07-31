// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t (/*AUTOARG*/);
   initial begin
      bit arr[];
      string v;
      bit [5:0] bit6 = 6'b111000;

      { >> bit {arr}} = bit6;
      v = $sformatf("%p", arr); `checks(v, "'{'h0, 'h0, 'h0, 'h1, 'h1, 'h1} ");

      { << bit {arr}} = bit6;
      v = $sformatf("%p", arr); `checks(v, "'{'h1, 'h1, 'h1, 'h0, 'h0, 'h0} ");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
