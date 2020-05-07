// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2015 by Johan Bjork.
// SPDX-License-Identifier: CC0-1.0

`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

interface a_if ();
   string s;
endinterface

module sub (output string s);
   initial s = $sformatf("%m");
endmodule

module t
  (
   clk
   );
   input clk;

   string str [2:0][1:0];

   a_if iface [2:0][1:0];

   sub i_sub[2:0][1:0] (.s(str));

   initial begin
      // TODO make self checking
      $display(iface[0][0]);
      $display(iface[0][1]);
      $display(iface[1][0]);
      $display(iface[1][1]);
      $display(iface[2][0]);
      $display(iface[2][1]);

      $display(str[0][0]);
      $display(str[0][1]);
      $display(str[1][0]);
      $display(str[1][1]);
      $display(str[2][0]);
      $display(str[2][1]);
   end
endmodule
