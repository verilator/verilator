// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);
`define checkg(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%g' exp='%g'\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc=0;

   integer i;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      begin
         // Type
         typedef bit [3:0] nibble_t;
         string a [nibble_t];
         string b [nibble_t];
         nibble_t k;
         string v;

         a[4'd3] = "fooed";
         a[4'd2] = "bared";
         i = a.num(); `checkh(i, 2);
         i = a.size; `checkh(i, 2);  // Also checks no parens
         v = a[4'd3]; `checks(v, "fooed");
         v = a[4'd2]; `checks(v, "bared");
         i = a.exists(4'd0); `checkh(i, 0);
         i = a.exists(4'd2); `checkh(i, 1);
         i = a.first(k); `checkh(i, 1); `checks(k, 4'd2);
         i = a.next(k); `checkh(i, 1); `checks(k, 4'd3);
         i = a.next(k); `checkh(i, 0);
         i = a.last(k); `checkh(i, 1); `checks(k, 4'd3);
         i = a.prev(k); `checkh(i, 1); `checks(k, 4'd2);
         i = a.prev(k); `checkh(i, 0);
         v = $sformatf("%p", a); `checks(v, "'{'h2:\"bared\", 'h3:\"fooed\"} ");

         a.delete(4'd2);
         i = a.size(); `checkh(i, 1);

         b = a;  // Copy assignment
         i = b.size(); `checkh(i, 1);
      end

      begin
         // Strings
         string a [string];
         string k;
         string v;

         a["foo"] = "fooed";
         a["bar"] = "bared";
         i = a.num(); `checkh(i, 2);
         i = a.size(); `checkh(i, 2);
         v = a["foo"]; `checks(v, "fooed");
         v = a["bar"]; `checks(v, "bared");
         i = a.exists("baz"); `checkh(i, 0);
         i = a.exists("bar"); `checkh(i, 1);
         i = a.first(k); `checkh(i, 1); `checks(k, "bar");
         i = a.next(k); `checkh(i, 1); `checks(k, "foo");
         i = a.next(k); `checkh(i, 0);
         i = a.last(k); `checkh(i, 1); `checks(k, "foo");
         i = a.prev(k); `checkh(i, 1); `checks(k, "bar");
         i = a.prev(k); `checkh(i, 0);
         v = $sformatf("%p", a["foo"]); `checks(v, "\"fooed\"");
         v = $sformatf("%p", a); `checks(v, "'{\"bar\":\"bared\", \"foo\":\"fooed\"} ");

         a.delete("bar");
         i = a.size(); `checkh(i, 1);
         a.delete();
         i = a.size(); `checkh(i, 0);
         i = a.first(k); `checkh(i, 0);
         i = a.last(k); `checkh(i, 0);

         // Patterns & default
`ifndef VERILATOR  // Unsupported: Pattern assignment
         a = '{ "f": "fooed", "b": "bared", default: "defaulted" };
         i = a.size(); `checkh(i, 2);  // Default doesn't count
         v = a["f"]; `checks(v, "fooed");
         v = a["b"]; `checks(v, "bared");
         v = a["NEXISTS"]; `checks(v, "defaulted");
`endif
      end

      begin
         // Wide-wides - need special array container classes, ick.
         logic [91:2] a [ logic [65:1] ];
         a[~65'hfe] = ~ 90'hfee;
         `checkh(a[~65'hfe], ~ 90'hfee);
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
