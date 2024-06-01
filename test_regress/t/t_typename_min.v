// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
   int unsigned array[3] = {1, 2, 3};
   int unsigned queue[$] = '{1, 2, 3};
   int unsigned q[$];
   int unsigned assoc[string] = '{"1":1, "2":2, "3":3};
   string s;
   initial begin
      s = $typename(array.min);
      `checks(s, "int$[$]");
      s = $sformatf("%p", array.min);
      `checks(s, "'{'h1} ");

      s = $typename(queue.min);
      `checks(s, "int$[$]");
      s = $sformatf("%p", queue.min);
      `checks(s, "'{'h1} ");

      s = $typename(assoc.min);
      `checks(s, "int$[$]");
      s = $sformatf("%p", assoc.min);
      `checks(s, "'{'h1} ");

      $write("*-* All Finished *-*\n");
      $finish;
  end
endmodule
