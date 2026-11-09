// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Interfaces declaring variables of their own virtual interface type

interface ifc;
  logic [6:0] r;
  modport mp(input r);
  function automatic bit same(virtual ifc o);
    virtual ifc v;
    virtual ifc.mp m;
    virtual ifc vs[2];
    v = o;
    m = o;
    vs[1] = o;
    return v == o && m.r == r && v.r == o.r && vs[1].r == o.r;
  endfunction
  class Holder;
    virtual ifc v;
  endclass
  function automatic logic [6:0] via_class(virtual ifc o);
    Holder h = new;
    h.v = o;
    return h.v.r;
  endfunction
endinterface

// Two interfaces referencing each other's virtual interface type
interface ifa;
  logic [6:0] r;
  function automatic logic [6:0] get(virtual ifb o);
    return o.s;
  endfunction
endinterface

interface ifb;
  logic [6:0] s;
  function automatic logic [6:0] get(virtual ifa o);
    return o.r;
  endfunction
endinterface

// Many functions with arguments of the interface's own virtual interface type, so the
// import must not copy each argument's import into the others
interface ifm;
  int r;
  function automatic int f0(virtual ifm o);
    return o.r + 0;
  endfunction
  function automatic int f1(virtual ifm o);
    return o.r + 1;
  endfunction
  function automatic int f2(virtual ifm o);
    return o.r + 2;
  endfunction
  function automatic int f3(virtual ifm o);
    return o.r + 3;
  endfunction
  function automatic int f4(virtual ifm o);
    return o.r + 4;
  endfunction
  function automatic int f5(virtual ifm o);
    return o.r + 5;
  endfunction
  function automatic int f6(virtual ifm o);
    return o.r + 6;
  endfunction
  function automatic int f7(virtual ifm o);
    return o.r + 7;
  endfunction
  function automatic int f8(virtual ifm o);
    return o.r + 8;
  endfunction
  function automatic int f9(virtual ifm o);
    return o.r + 9;
  endfunction
  function automatic int f10(virtual ifm o);
    return o.r + 10;
  endfunction
  function automatic int f11(virtual ifm o);
    return o.r + 11;
  endfunction
  function automatic int f12(virtual ifm o);
    return o.r + 12;
  endfunction
  function automatic int f13(virtual ifm o);
    return o.r + 13;
  endfunction
  function automatic int f14(virtual ifm o);
    return o.r + 14;
  endfunction
  function automatic int f15(virtual ifm o);
    return o.r + 15;
  endfunction
  function automatic int f16(virtual ifm o);
    return o.r + 16;
  endfunction
  function automatic int f17(virtual ifm o);
    return o.r + 17;
  endfunction
  function automatic int f18(virtual ifm o);
    return o.r + 18;
  endfunction
  function automatic int f19(virtual ifm o);
    return o.r + 19;
  endfunction
endinterface

// Typedefs of the interface's own virtual interface type
package pkg;
  typedef virtual ift vif_t;
endpackage

interface ift;
  int r;
  modport mp(input r);
  typedef virtual ift vif_t;
  typedef vif_t vif2_t;
  typedef virtual ift.mp vifm_t;
  typedef virtual ift vifa_t[2];
  vif_t self;
  vif2_t self2;
  vifm_t selfm;
  vifa_t selfa;
  pkg::vif_t selfp;
  function automatic int sum(vif_t o);
    vif2_t v;
    v = o;
    return v.r + self.r + self2.r + selfm.r + selfa[1].r + selfp.r;
  endfunction
endinterface

class Cls;
  virtual ifc v;
  pkg::vif_t t;
endclass

// Accesses through an interface port into interfaces nested in that interface
interface inner;
  int x;
  modport mp(output x);
endinterface

interface mid;
  inner sub ();
endinterface

interface outer (
    inner p,
    inner.mp pm
);
  int x;  // Same name as inner's x, which the nested accesses below must not resolve to
  inner sub ();
  inner subs[2] ();
  mid md ();
  virtual inner vref;
  virtual inner.mp vrefm;
  virtual inner vrefs[2];
  modport mp(input x);
endinterface

module sub_access (
    outer o,
    outer.mp om
);
  initial begin
    virtual mid vm;
    #1;
    o.x = 1;
    o.p.x = 2;
    o.sub.x = 3;
    o.subs[1].x = 4;
    o.md.sub.x = 5;
    o.vref = o.sub;
    o.vrefm = o.sub;
    o.vrefs[1] = o.md.sub;
    vm = o.md;
    #1;
    `checkd(om.x, 1);
    `checkd(o.p.x, 2);
    `checkd(o.pm.x, 2);
    `checkd(o.sub.x, 3);
    `checkd(o.subs[1].x, 4);
    `checkd(o.md.sub.x, 5);
    `checkd(o.vref.x, 3);
    `checkd(o.vrefm.x, 3);
    `checkd(o.vrefs[1].x, 5);
    `checkd(vm.sub.x, 5);
    o.vref.x = 6;
    vm.sub.x = 7;
    `checkd(o.sub.x, 6);
    `checkd(o.md.sub.x, 7);
  end
endmodule

module t;
  initial begin
    #3;  // After sub_access's checks
    $write("*-* All Finished *-*\n");
    $finish;
  end

  ifc i ();
  ifc j ();
  initial begin
    automatic Cls c = new;
    c.v = i;
    i.r = 7'h15;
    j.r = 7'h2a;
    `checkh(i.same(i), 1'b1);
    `checkh(i.same(j), 1'b0);
    `checkh(c.v.same(i), 1'b1);
    `checkh(c.v.same(j), 1'b0);
    `checkh(i.via_class(j), 7'h2a);
  end

  ifa a ();
  ifb b ();
  initial begin
    a.r = 7'h4c;
    b.s = 7'h33;
    `checkh(a.get(b), 7'h33);
    `checkh(b.get(a), 7'h4c);
  end

  ifm m ();
  initial begin
    m.r = 5;
    `checkd(m.f19(m), 24);
  end

  ift ti ();
  ift tj ();
  initial begin
    automatic Cls c = new;
    c.t = ti;
    ti.r = 1;
    tj.r = 10;
    ti.self = tj;
    ti.self2 = tj;
    ti.selfm = tj;
    ti.selfa[1] = tj;
    ti.selfp = tj;
    `checkd(ti.sum(ti), 51);
    `checkd(c.t.sum(tj), 60);
  end

  inner in ();
  outer ou (
      in,
      in
  );
  sub_access u (
      .o(ou),
      .om(ou)
  );
endmodule
