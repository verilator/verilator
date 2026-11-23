// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A method called through a virtual interface runs on the instance the handle selects

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface sub_ifc;
  int z = -3;
  int w = -4;
  function void setw(int v);
    w = v;
  endfunction
endinterface

interface ifc (
    input logic clk
);
  int x = -1;
  int y = -2;
  int sig;
  sub_ifc s ();
  clocking cb @(posedge clk);
    input sig;
  endclocking
  function void setx(int v);
    x = v;
  endfunction
  function void sety(int v);
    y <= v;
  endfunction
  function int getx();
    return x;
  endfunction
  function void setz(int v);
    s.z = v;
  endfunction
  function int getz();
    return s.z;
  endfunction
  import "DPI-C" function int dpic_add1(int v);
  import "DPI-C" context function string dpic_scope();
  function string scope();
    return dpic_scope();
  endfunction
  task automatic sample(output int got, output time t);
    @(cb);
    got = cb.sig;
    t = $time;
  endtask
  // An upward reference out of the interface is illegal here: "Although an interface may
  // contain hierarchical references to objects outside its body or ports that reference other
  // interfaces, it shall be illegal to use an interface containing those references in the
  // declaration of a virtual interface." (IEEE 1800-2023 25.9)
  // function logic get_up();
  //   return holder.clk;
  // endfunction
endinterface

module holder (
    input logic clk
);
  ifc i (clk);
endmodule

class Drv;
  virtual ifc vif;
  function new(virtual ifc v);
    vif = v;
  endfunction
  function void setx(int v);
    vif.setx(v);
  endfunction
  function void sety(int v);
    vif.sety(v);
  endfunction
  function int getx();
    return vif.getx();
  endfunction
  task sample(output int got, output time t);
    vif.sample(got, t);
  endtask
endclass

module t;
  logic clk_a = 0;
  logic clk_b = 0;
  always #5 clk_a = ~clk_a;
  always #10 clk_b = ~clk_b;

  holder ha (clk_a);
  holder hb (clk_b);

  // Combinational logic reading what the methods write
  wire integer xa1 = ha.i.x + 1;
  wire integer xb1 = hb.i.x + 1;

  // Calls with no time passing around them
  initial begin
    virtual ifc v;
    v = ha.i;
    ha.i.x = 7;
    v.setx(8);
    `checkd(ha.i.x, 8);
    `checkd(v.getx(), 8);
  end

  // A call from a static initializer, which runs before any initial block
  virtual ifc vinit = hb.i;
  string sinit = vinit.scope();
  initial begin
    `checks(sinit, "t.hb.i");
  end

  // Calls from logic that cannot suspend, read by logic the scheduler has to re-evaluate
  holder hc (clk_a);
  virtual ifc vc = hc.i;
  int ncalls = 0;
  always @(posedge clk_a) begin
    ncalls <= ncalls + 1;
    vc.setx(ncalls + 100);
  end
  wire integer xdirect = hc.i.x + 1;  // Reads the instance
  int xdirect_seen = 0;
  always @(xdirect) xdirect_seen = xdirect;
  always @(negedge clk_a) begin
    `checkd(xdirect_seen, ncalls + 100);
  end
`ifdef VERILATOR
  // Reads only through the handle. IEEE 1800-2023 25.9 does not allow a member selected
  // through a handle in a continuous assignment, but Verilator supports it. Probably
  // shouldn't ...
  wire integer xhandle = vc.x + 1;
  int xhandle_seen = 0;
  always @(xhandle) xhandle_seen = xhandle;
  always @(negedge clk_a) begin
    `checkd(xhandle_seen, ncalls + 100);
  end
`endif

  // Calls from a class
  bit sampled = 0;  // The calls waiting for a clocking event returned
  initial begin
    Drv da;
    Drv db;
    da = new(ha.i);
    db = new(hb.i);
    ha.i.sig = 11;
    hb.i.sig = 22;
    #1;
    da.setx(1);
    `checkd(ha.i.x, 1);
    `checkd(hb.i.x, -1);
    db.setx(2);
    `checkd(ha.i.x, 1);
    `checkd(hb.i.x, 2);
    `checkd(da.getx(), 1);
    `checkd(db.getx(), 2);
    da.sety(3);
    `checkd(ha.i.y, -2);
    `checkd(hb.i.y, -2);
    #1;  // For the NBA, and the combinational logic
    `checkd(ha.i.y, 3);
    `checkd(hb.i.y, -2);
    `checkd(xa1, 2);
    `checkd(xb1, 3);
    db.sety(4);
    `checkd(ha.i.y, 3);
    `checkd(hb.i.y, -2);
    #1;  // For the NBA
    `checkd(ha.i.y, 3);
    `checkd(hb.i.y, 4);
    // Each waits for the clocking event of its own instance
    fork
      begin
        int got;
        time t;
        da.sample(got, t);
        `checkd(got, 11);
        `checkd(t, 5);
      end
      begin
        int got;
        time t;
        db.sample(got, t);
        `checkd(got, 22);
        `checkd(t, 10);
      end
    join
    sampled = 1;
  end

  // Calls from a module
  initial begin
    virtual ifc va;
    virtual ifc vb;
    va = ha.i;
    vb = hb.i;
    #20;
    va.setx(5);
    `checkd(ha.i.x, 5);
    `checkd(hb.i.x, 2);
    vb.setx(6);
    `checkd(ha.i.x, 5);
    `checkd(hb.i.x, 6);
    va.setz(9);
    `checkd(ha.i.s.z, 9);
    `checkd(hb.i.s.z, -3);
    vb.setz(10);
    `checkd(ha.i.s.z, 9);
    `checkd(hb.i.s.z, 10);
    `checkd(va.getz(), 9);
    `checkd(vb.getz(), 10);
    `checks(va.scope(), "t.ha.i");
    `checks(vb.scope(), "t.hb.i");
    `checkd(va.dpic_add1(1), 2);
    // A method of a nested interface, selected through the handle
    va.s.setw(11);
    `checkd(ha.i.s.w, 11);
    `checkd(hb.i.s.w, -4);
    vb.s.setw(12);
    `checkd(ha.i.s.w, 11);
    `checkd(hb.i.s.w, 12);
    va.sety(7);
    `checkd(ha.i.y, 3);
    `checkd(hb.i.y, 4);
    #1;  // For the NBA, and the combinational logic
    `checkd(ha.i.y, 7);
    `checkd(hb.i.y, 4);
    `checkd(xa1, 6);
    `checkd(xb1, 7);
    vb.sety(8);
    `checkd(ha.i.y, 7);
    `checkd(hb.i.y, 4);
    #1;  // For the NBA
    `checkd(ha.i.y, 7);
    `checkd(hb.i.y, 8);
    // After re-assigning the handle, its calls run on the other instance
    va = vb;
    va.setx(13);
    `checkd(ha.i.x, 5);
    `checkd(hb.i.x, 13);
    `checkd(va.getx(), 13);
    va.s.setw(14);
    `checkd(ha.i.s.w, 11);
    `checkd(hb.i.s.w, 14);
    `checkd(va.getz(), 10);
    `checks(va.scope(), "t.hb.i");
    va.sety(15);
    `checkd(ha.i.y, 7);
    `checkd(hb.i.y, 8);
    #1;  // For the NBA
    `checkd(ha.i.y, 7);
    `checkd(hb.i.y, 15);
  end

  initial begin
    #30;
    `checkd(sampled, 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
