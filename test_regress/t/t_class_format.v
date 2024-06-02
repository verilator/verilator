// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2021 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
 `define stop $stop
`else
 `define stop
`endif
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Cls;
   bit b;
   int i;
   bit [15:0] carray4 [4];
   bit [64:0] cwide[2];
   string     name;
   task debug();
      $display("DEBUG: %s (@%0t) %s", this.name, $realtime, "message");
   endtask
endclass

module t (/*AUTOARG*/);
   initial begin
      Cls c;
      c = new;
      c.b = '1;
      c.i = 42;
      c.name = "object_name";

      c.carray4[0] = 16'h11;
      c.carray4[1] = 16'h22;
      c.carray4[2] = 16'h33;
      c.carray4[3] = 16'h44;
      $display("'%p'", c);

      c.carray4 = '{16'h911, 16'h922, 16'h933, 16'h944};
      $display("'%p'", c);

      c.debug();

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
