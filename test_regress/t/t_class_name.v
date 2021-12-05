// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2020 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef verilator
 `define stop $stop
`else
 `define stop
`endif
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

function string unit_name;
   return $sformatf("u %m");
endfunction

class Cls;
   // We use the same name for all static_name's to check we resolve right
   static function string static_name;
      return $sformatf("c %m");
   endfunction
   // Different for non_statis to make sure likewise
   function string c_auto_name;
      return $sformatf("c %m");
   endfunction
endclass

package P;
class Cls;
   static function string static_name;
      return $sformatf("p %m");
   endfunction
   function string p_auto_name;
      return $sformatf("p %m");
   endfunction
endclass
endpackage

module M;
class Cls;
   static function string static_name;
      return $sformatf("m %m");
   endfunction
   function string m_auto_name;
      return $sformatf("m %m");
   endfunction
endclass
   S sub();
   function string cls_static_name;
      return Cls::static_name();
   endfunction
   function string cls_auto_name;
      Cls c;
      c = new;
      return c.m_auto_name();
   endfunction
endmodule

module S;
class Cls;
   static function string static_name;
      return $sformatf("ms %m");
   endfunction
   function string ms_auto_name;
      return $sformatf("ms %m");
   endfunction
endclass
   function string cls_static_name;
      return Cls::static_name();
   endfunction
   function string cls_auto_name;
      Cls c;
      c = new;
      return c.ms_auto_name();
   endfunction
endmodule

module t (/*AUTOARG*/);
   string s;

   M m();

   function string mod_func_name;
      return $sformatf("tmf %m");
   endfunction

   initial begin
      Cls c;
      P::Cls p;
      p = new;
      c = new;

      s = mod_func_name();
      `checks(s, "tmf top.t.mod_func_name");

      s = unit_name();
      `checks(s, "u top.$unit.unit_name");
      // Others: "u $unit_????::unit_name
      // Others: "u $unit::unit_name
      // Others: "u \\package UnitScopePackage_1\ .UnitScopePackage_1.unit_name

      // *** Below results vary with simulator.

      s = Cls::static_name();
      `checks(s, "c top.$unit.Cls.static_name");
      // Others: "c $unit_????.Cls.static_name
      // Others: "c $unit::\Cls::static_name
      // Others: "c Cls.static_name
      s = c.c_auto_name();
      `checks(s, "c top.$unit.Cls.c_auto_name");
      // Others: "c $unit_????.Cls.c_auto_name
      // Others: "c $unit::\Cls::c_auto_name
      // Others: "c Cls.c_auto_name

      //UNSUP s = P::Cls::static_name();
      //UNSUP `checks(s, "p top.P.Cls");
      // UNSUP `checks(s, "p top.P.Cls.static_name");
      // Others: "p P.Cls.static_name
      // Others: "p P::Cls.static_name
      // Others: "p P::\Cls::static_name
      // Others: "p \\package P\ .Cls.static_name

      s = p.p_auto_name();
      `checks(s, "p top.P.Cls.p_auto_name");
      // Others: "p P.Cls.p_auto_name
      // Others: "p P::Cls.p_auto_name
      // Others: "p P::\Cls::p_auto_name
      // Others: "p \\package P\ .Cls.p_auto_name

      s = m.cls_static_name();
      `checks(s, "m top.t.m.Cls.static_name");
      // Others: "m top.t.m.Cls.static_name
      // Others: "m top.t.m.\Cls::static_name

      s = m.cls_auto_name();
      `checks(s, "m top.t.m.Cls.m_auto_name");
      // Others: "m top.t.m.Cls.m_auto_name
      // Others: "m top.t.m.\Cls::m_auto_name

      s = m.sub.cls_static_name();
      `checks(s, "ms top.t.m.sub.Cls.static_name");
      // Others: "ms top.t.m.sub.Cls.static_name
      // Others: "ms top.t.m.sub.\Cls::static_name
      s = m.sub.cls_auto_name();
      `checks(s, "ms top.t.m.sub.Cls.ms_auto_name");
      // Others: "ms top.t.m.sub.Cls.ms_auto_name
      // Others: "ms top.t.m.sub.\Cls::ms_auto_name

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
