// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Classes of the same name in different scopes, as type parameter values, make different
// specializations

package PkgReg;
  class Registry #(
      type T = int
  );
    static function T create();
      T h = new;
      return h;
    endfunction
  endclass
  class Db #(
      type T = int
  );
    static T m_v;
    static function void set(T value);
      m_v = value;
    endfunction
  endclass
endpackage

package PkgA;
  class Cfg;
    typedef PkgReg::Registry#(Cfg) type_id;
    virtual function string who();
      return "PkgA::Cfg";
    endfunction
  endclass
  class Outer;
    class Item;
      virtual function string who();
        return "PkgA::Outer::Item";
      endfunction
    endclass
  endclass
  class Other;
    class Item;
      virtual function string who();
        return "PkgA::Other::Item";
      endfunction
    endclass
  endclass
  class Pc #(
      type T = int
  );
    virtual function string who();
      return "PkgA::Pc";
    endfunction
  endclass
  class Base;
  endclass
  class Data extends Base;
    virtual function string who();
      return "PkgA::Data";
    endfunction
  endclass
  function automatic void setData();
    Data h = new;
    PkgReg::Db#(Data)::set(h);
  endfunction
endpackage

package PkgB;
  class Cfg;
    typedef PkgReg::Registry#(Cfg) type_id;
    virtual function string who();
      return "PkgB::Cfg";
    endfunction
  endclass
  class Outer;
    class Item;
      virtual function string who();
        return "PkgB::Outer::Item";
      endfunction
    endclass
  endclass
  class Pc #(
      type T = int
  );
    virtual function string who();
      return "PkgB::Pc";
    endfunction
  endclass
  class Data;
    virtual function string who();
      return "PkgB::Data";
    endfunction
  endclass
endpackage

// A package and a module of the same name
package dup;
  class Cfg;
    virtual function string who();
      return "package dup";
    endfunction
  endclass
endpackage

module dup;
  class Cfg;
    virtual function string who();
      return "module dup";
    endfunction
  endclass
  function automatic string who();
    Cfg h = PkgReg::Registry#(Cfg)::create();
    return h.who();
  endfunction
endmodule

class Cfg;
  typedef PkgReg::Registry#(Cfg) type_id;
  virtual function string who();
    return "$unit::Cfg";
  endfunction
endclass

// Each instance declares its own Cfg
interface Ifc #(
    int W = 1
);
  class Cfg;
    virtual function int width();
      return W;
    endfunction
  endclass
  function automatic int width();
    Cfg h = PkgReg::Registry#(Cfg)::create();
    return h.width();
  endfunction
endinterface

// Each specialization declares its own Cfg
module sub #(
    parameter string NAME = ""
);
  class Cfg;
    virtual function string who();
      return NAME;
    endfunction
  endclass
  function automatic string who();
    Cfg h = PkgReg::Registry#(Cfg)::create();
    return h.who();
  endfunction
endmodule

module t;
  dup u_dup ();
  sub #(.NAME("s1")) s1 ();
  sub #(.NAME("s2")) s2 ();

  for (genvar i = 0; i < 2; i++) begin : g
    class Cfg;
      virtual function string who();
        return $sformatf("g[%0d]", i);
      endfunction
    endclass
    function automatic string who();
      Cfg h = PkgReg::Registry#(Cfg)::create();
      return h.who();
    endfunction
  end

  // Same-named classes in unnamed generate blocks
  if (1) begin
    class Cfg;
      virtual function string who();
        return "unnamed1";
      endfunction
    endclass
    final begin
      automatic Cfg h = PkgReg::Registry#(Cfg)::create();
      `checks(h.who(), "unnamed1");
    end
  end
  if (1) begin
    class Cfg;
      virtual function string who();
        return "unnamed2";
      endfunction
    endclass
    final begin
      automatic Cfg h = PkgReg::Registry#(Cfg)::create();
      `checks(h.who(), "unnamed2");
    end
  end

  // Classes declared in instances of an interface
  Ifc #(.W(3)) i3 ();
  Ifc #(.W(7)) i7 ();

  initial begin
    // Same-named classes in different packages, and in $unit
    begin
      automatic PkgA::Cfg a = PkgA::Cfg::type_id::create();
      automatic PkgB::Cfg b = PkgB::Cfg::type_id::create();
      automatic Cfg u = Cfg::type_id::create();
      `checks(a.who(), "PkgA::Cfg");
      `checks(b.who(), "PkgB::Cfg");
      `checks(u.who(), "$unit::Cfg");
    end

    // Same-named nested classes
    begin
      automatic PkgA::Outer::Item ai = PkgReg::Registry#(PkgA::Outer::Item)::create();
      automatic PkgB::Outer::Item bi = PkgReg::Registry#(PkgB::Outer::Item)::create();
      automatic PkgA::Other::Item oi = PkgReg::Registry#(PkgA::Other::Item)::create();
      `checks(ai.who(), "PkgA::Outer::Item");
      `checks(bi.who(), "PkgB::Outer::Item");
      `checks(oi.who(), "PkgA::Other::Item");
    end

    // Specializations of same-named parameterized classes
    begin
      automatic PkgA::Pc #(int) ap = PkgReg::Registry#(PkgA::Pc#(int))::create();
      automatic PkgB::Pc #(int) bp = PkgReg::Registry#(PkgB::Pc#(int))::create();
      `checks(ap.who(), "PkgA::Pc");
      `checks(bp.who(), "PkgB::Pc");
    end

    // Same-named classes, one with a base class, as static function arguments
    begin
      automatic PkgB::Data b = new;
      PkgA::setData();
      PkgReg::Db#(PkgB::Data)::set(b);
      `checks(PkgReg::Db#(PkgA::Data)::m_v.who(), "PkgA::Data");
      `checks(PkgReg::Db#(PkgB::Data)::m_v.who(), "PkgB::Data");
    end

    // Same-named classes in a package and a module of the same name
    begin
      automatic dup::Cfg d = PkgReg::Registry#(dup::Cfg)::create();
      `checks(d.who(), "package dup");
      `checks(u_dup.who(), "module dup");
    end

    // Same-named classes in instances of a module, and in generate blocks
    `checks(s1.who(), "s1");
    `checks(s2.who(), "s2");
    `checks(g[0].who(), "g[0]");
    `checks(g[1].who(), "g[1]");

    // Containers of same-named classes, as type parameter values of a class
    begin
      typedef PkgA::Data a_da_t[];
      typedef PkgB::Data b_da_t[];
      typedef PkgA::Data a_wa_t [*];
      typedef PkgB::Data b_wa_t [*];
      typedef PkgA::Data a_u_t[3:1];
      typedef PkgB::Data b_u_t[3:1];
      automatic PkgA::Data da = new;
      automatic PkgB::Data db = new;
      PkgReg::Db#(a_da_t)::m_v = new[1];
      PkgReg::Db#(b_da_t)::m_v = new[1];
      PkgReg::Db#(a_da_t)::m_v[0] = da;
      PkgReg::Db#(b_da_t)::m_v[0] = db;
      PkgReg::Db#(a_wa_t)::m_v[5] = da;
      PkgReg::Db#(b_wa_t)::m_v[5] = db;
      PkgReg::Db#(a_u_t)::m_v[2] = da;
      PkgReg::Db#(b_u_t)::m_v[2] = db;
      `checks(PkgReg::Db#(a_da_t)::m_v[0].who(), "PkgA::Data");
      `checks(PkgReg::Db#(b_da_t)::m_v[0].who(), "PkgB::Data");
      `checks(PkgReg::Db#(a_wa_t)::m_v[5].who(), "PkgA::Data");
      `checks(PkgReg::Db#(b_wa_t)::m_v[5].who(), "PkgB::Data");
      `checks(PkgReg::Db#(a_u_t)::m_v[2].who(), "PkgA::Data");
      `checks(PkgReg::Db#(b_u_t)::m_v[2].who(), "PkgB::Data");
    end

    // Classes declared in instances of an interface
    `checkd(i3.width(), 3);
    `checkd(i7.width(), 7);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
