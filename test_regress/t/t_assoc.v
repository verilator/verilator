// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2019 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   integer cyc = 0;

   integer i;

   always @ (posedge clk) begin
      cyc <= cyc + 1;
      begin
         // Type
         typedef bit [3:0] nibble_t;
         typedef string dict_t [nibble_t];
         dict_t a;
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
         `checkp(a, "'{'h2:\"bared\", 'h3:\"fooed\"} ");

         a.first(k); `checks(k, 4'd2);
         a.next(k); `checks(k, 4'd3);
         a.next(k);
         a.last(k); `checks(k, 4'd3);
         a.prev(k); `checks(k, 4'd2);

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
         `checkp(a["foo"], "\"fooed\"");
         `checkp(a, "'{\"bar\":\"bared\", \"foo\":\"fooed\"} ");

         a.delete("bar");
         i = a.size(); `checkh(i, 1);
         a.delete();
         i = a.size(); `checkh(i, 0);
         i = a.first(k); `checkh(i, 0);
         i = a.last(k); `checkh(i, 0);

         // Patterns & default
         a = '{ "f": "fooed", "b": "bared", default: "defaulted" };
         i = a.size(); `checkh(i, 2);  // Default doesn't count
         v = a["f"]; `checks(v, "fooed");
         v = a["b"]; `checks(v, "bared");
         v = a["NEXISTS"]; `checks(v, "defaulted");

         a = '{};
         i = a.size(); `checkh(i, 0);
      end

      begin
         // Wide-wides - need special array container classes, ick.
         logic [91:2] a [ logic [65:1] ];
         int          b [ bit [99:0] ];
         a[~65'hfe] = ~ 90'hfee;
         `checkh(a[~65'hfe], ~ 90'hfee);
         b[100'b1] = 1;
         `checkh(b[100'b1], 1);
      end

      begin
         int a [string];
         int sum;
         sum = 0;
         a["one"] = 1;
         a["two"] = 2;
         foreach (a[i]) sum += a[i];
         `checkh(sum, 1 + 2);
      end

      begin   // Issue #5435
         int a;
         int ok;
         int dict [int];

         dict[3] = 'h13;
         dict[4] = 'h14;
         dict[5] = 'h15;

         a = 4;
         ok = dict.first(a);
         if (a != 3) $stop;
         if (ok != 1) $stop;
         a = 4;
         ok = dict.next(a);
         if (a != 5) $stop;
         if (ok != 1) $stop;
         a = 4;
         ok = dict.last(a);
         if (a != 5) $stop;
         if (ok != 1) $stop;
      end

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
