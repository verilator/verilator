// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2009-2023 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checks(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

class Cls;
   typedef struct {
      string      m_strg;
   } underclass_t;

   underclass_t m_cstr;
   function underclass_t get_cstr();
      m_cstr.m_strg = "foo";
      return m_cstr;
   endfunction
endclass


module x;
   typedef struct {
      int a, b;
      logic [3:0] c;
   } embedded_t;

   typedef struct {
      embedded_t b;
      embedded_t tab [3:0];
   } notembedded_t;

   typedef struct {
      logic [15:0] m_i;
      string       m_s;
   } istr_t;

   notembedded_t p;
   embedded_t t [1:0];
   istr_t istr;
   string s;
   Cls c;

   initial begin
      t[1].a = 2;
      p.b.a = 1;
      if (t[1].a != 2) $stop;
      if (p.b.a != 1) $stop;

      istr.m_i = 12;
      istr.m_s = "str1";
      s = $sformatf("%p", istr);
      `checks(s, "'{m_i:'hc, m_s:\"str1\"}");

      istr = '{m_i: '1, m_s: "str2"};
      s = $sformatf("%p", istr);
      `checks(s, "'{m_i:'hffff, m_s:\"str2\"}");

      c = new;
      s = c.get_cstr().m_strg;
      `checks(s, "foo");

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
