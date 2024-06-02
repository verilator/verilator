// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

typedef struct {
   struct {
      struct {
         logic [31:0] next;
      } val;
   } el[1];
} pstr_t;

module t (/*AUTOARG*/);

   typedef struct {
      struct {
         struct {
            logic [31:0] next;
         } val;
      } el[1];
   } str_t;

   str_t str;
   pstr_t pstr;

   initial begin
      string s;

      str.el[0].val.next = 6;
      s = $sformatf("%p", str);
      $display("%s", s);
      `checks(s, "'{el:'{'{val:'{next:'h6}}} }");

      pstr.el[0].val.next = 6;
      s = $sformatf("%p", pstr);
      $display("%s", s);
      `checks(s, "'{el:'{'{val:'{next:'h6}}} }");

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
