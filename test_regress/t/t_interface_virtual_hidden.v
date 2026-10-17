// DESCRIPTION: Verilator: Accesses through virtual interfaces are seen by the analyses, so
// processes reading and writing members through them are ordered and evaluated again as needed
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface cbus;
  // verilator lint_off UNOPTFLAT
  logic [7:0] x;  // In a loop below
  // verilator lint_on UNOPTFLAT
endinterface

interface ebus (
    input bit clk
);
  logic [7:0] x;
endinterface

interface bus;
  logic [7:0] y;
endinterface

interface pbus (
    input bit clk
);
  logic [7:0] cnt = 0;
  always @(posedge clk) cnt <= cnt + 1;
endinterface

interface sbus;
  bus s ();
endinterface

interface tbus;
  logic [7:0] y;
endinterface

interface kbus;
  logic clk = 0;
  logic [7:0] d = 0;
  logic [7:0] q;
  always @(posedge clk) q <= d;
endinterface

interface qbus #(
    parameter int W = 8
);
  logic [W-1:0] y;
  modport mp(output y);
endinterface

interface wbus;
  int x1, x2, x3, x4, x5, x6, x8;
  struct packed {
    logic [7:0] f;
    logic [7:0] g;
  } st;
endinterface

// Reads, through a virtual interface, the instance connected to the port
module binder (
    input bit clk,
    pbus p
);
  virtual pbus v;
  logic [7:0] seen;
  initial v = p;
  always @(posedge clk) seen <= v.cnt;
endmodule

module t;
  bit clk;
  int cyc;
  always #5 clk = ~clk;

  // Combinational logic writing through one virtual interface and reading through another,
  // which may point to the same instance: a loop that scheduling must break. Its values are not
  // checked, as IEEE 1800-2023 9.2.2.2.1 makes only the handles sensitivities of always_comb.
  cbus ca (), cb ();
  virtual cbus va = ca, vb = cb;
  // verilator lint_off UNOPTFLAT
  logic [7:0] y;
  // verilator lint_on UNOPTFLAT
  always_comb va.x = y;
  always_comb y = vb.x;
  initial #1000 vb = ca;

  // Combinational logic reading one instance through a virtual interface and writing another:
  // not a loop, as the virtual interface never points to the instance written
  bus ri (), ro ();
  virtual bus vro = ro, vri = ri;
  always_comb ri.y = vro.y + 8'(cyc);
  always @(posedge clk) ro.y <= ri.y;

  // A possible write through a virtual interface does not make the read after it of the block
  // itself: the block still depends on the member, and is not constant
  bus wa (), wb ();
  virtual bus vw = wa;
  initial #1 vw = wb;
  logic [7:0] data_w = 8'd123;
  logic [7:0] out_w;
  always @* begin
    vw.y = data_w;
    out_w = wa.y;
  end
  always @(posedge clk) wa.y <= 8'(cyc);
  // Nor turns an explicit sensitivity list into a combinational one, sensitive to the member
  bus xa (), xb ();
  virtual bus vx = xa;
  initial #1 vx = xb;
  logic [7:0] data_x, out_x, exp_x;
  always @(data_x) begin
    vx.y = data_x;
    out_x = xa.y;
  end
  always @(posedge clk) xa.y <= 8'(cyc);

  // Event controls through a virtual interface that is null until an initial process sets it
  ebus ec (.clk);
  virtual ebus vc;
  initial vc = ec;
  logic [7:0] seen_c;
  logic [7:0] cnt_c = 0;
  always @(vc.x) begin
    seen_c = vc.x * 8'd3;
    if (seen_c > 8'd5) seen_c = seen_c - 8'd1;
  end
  initial forever @(posedge vc.clk) cnt_c <= cnt_c + 1;

  // Bound through an interface port, read before the NBA updates of the instance
  pbus pd (.clk);
  binder bind_d (
      .clk,
      .p(pd)
  );
  // Bound by an array of instances, read before the NBA updates of the instance
  pbus pa[2] (.clk);
  virtual pbus vpa[2];
  int k = 1;
  logic [7:0] seen_a;
  initial vpa = pa;
  always @(posedge clk) seen_a <= vpa[k].cnt;

  // A blocking write through a virtual interface, then an NBA to the same member, which is last
  bus f ();
  virtual bus vf = f;
  always @(posedge clk) begin
    f.y <= 8'(cyc);
    vf.y = 8'hff;
  end
  // The same through a sub-interface of a virtual interface
  sbus g ();
  virtual sbus vg = g;
  always @(posedge clk) begin
    g.s.y <= 8'(cyc);
    vg.s.y = 8'hff;
  end

  // A member forced and released, and read through a virtual interface
  bus fo ();
  virtual bus vfo = fo;
  logic [7:0] seen_fo;
  initial begin
    fo.y = 8'd1;
    force fo.y = 8'd2;
    #1 release fo.y;
    fo.y = 8'd3;
    #1 seen_fo = vfo.y;
  end

  // A write through a virtual interface between a write and a read of the member, which must not
  // read the first write; and a read through it between two writes
  bus la (), lb ();
  virtual bus vla = la, vlb = lb;
  logic [7:0] seen_la, seen_lb;
  always @(posedge clk) begin
    la.y = 8'd5;
    vla.y = 8'(cyc);
    seen_la <= la.y;
  end
  always @(posedge clk) begin
    lb.y = 8'd7;
    seen_lb <= vlb.y;
    lb.y = 8'(cyc);
  end

  // Other forms of writes through a virtual interface, between a write and a read of the member
  wbus wf ();
  virtual wbus vwf = wf;
  int s1, s2, s4, s5, s6, s8;
  logic [7:0] s9;
  task automatic incr(ref int r);
    r = r + 1;
  endtask
  task automatic setio(inout int r);
    r = r + 2;
  endtask
  always @(posedge clk) begin
    wf.x1 = 5;
    void'($sscanf("7", "%d", vwf.x1));
    s1 <= wf.x1;
    wf.x2 = 5;
    {vwf.x2[3:0], vwf.x3[3:0]} = 8'h21;
    s2 <= wf.x2;
    wf.x4 = 5;
    incr(vwf.x4);
    s4 <= wf.x4;
    wf.x5 = 5;
    setio(vwf.x5);
    s5 <= wf.x5;
    wf.x6 = 5;
    vwf.x6++;
    s6 <= wf.x6;
    wf.x8 = 5;
    vwf.x8 += 3;
    s8 <= wf.x8;
    wf.st = 16'h0505;
    vwf.st.f = 8'h11;
    s9 <= wf.st.f;
  end

  // A blocking write through a virtual interface as a task output, then an NBA to the member;
  // the NBA in the task is not through the virtual interface
  tbus to ();
  virtual tbus vto = to;
  logic [7:0] q_to;
  task automatic set_ff(output logic [7:0] o);
    o = 8'hff;
    q_to <= 8'(cyc);
  endtask
  always @(posedge clk) begin
    to.y <= 8'(cyc);
    set_ff(vto.y);
  end

  // Parameterized interfaces, and a modport
  qbus #(.W(16)) qf ();
  qbus #(.W(8)) qe ();
  virtual qbus #(.W(16)) vqf = qf;
  virtual qbus #(.W(8)).mp vqe = qe;
  logic [15:0] seen_q;
  always @(posedge clk) begin
    qf.y <= 16'(cyc);
    vqf.y = 16'hffff;
  end
  always @(posedge clk) begin
    qe.y <= 8'(cyc);
    vqe.y = 8'hff;
  end
  always @(posedge clk) begin
    qf.y = 16'd5;
    vqf.y = 16'(cyc);
    seen_q <= qf.y;
  end

  // Clocks driven through virtual interfaces
  kbus ka (), kb ();
  virtual kbus vka = ka, vkb = kb;
  int cnt_ka = 0, cnt_kb = 0;
  logic [7:0] seen_k;
  initial forever #5 vka.clk = ~vka.clk;
  initial forever #7 vkb.clk = ~vkb.clk;
  always @(posedge ka.clk) begin
    cnt_ka <= cnt_ka + 1;
    ka.d <= ka.d + 1;
    seen_k <= vka.q;
  end
  always @(posedge kb.clk) cnt_kb <= cnt_kb + 1;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    cb.x <= 8'(cyc);
    ec.x <= 8'(cyc);
  end

  always @(negedge clk) begin
    if (cyc >= 1) begin
      `checkd(seen_c, ec.x * 8'd3 > 8'd5 ? ec.x * 8'd3 - 8'd1 : ec.x * 8'd3);
      `checkd(cnt_c, 8'(cyc));
      `checkd(f.y, 8'(cyc - 1));
      `checkd(g.s.y, 8'(cyc - 1));
      `checkd(bind_d.seen, 8'(cyc - 1));
      `checkd(seen_a, 8'(cyc - 1));
      `checkd(ri.y, ro.y + 8'(cyc));
      `checkd(out_w, 8'(cyc - 1));
      `checkd(seen_la, 8'(cyc - 1));
      `checkd(seen_lb, 8'd7);
      `checkd(lb.y, 8'(cyc - 1));
      `checkd(s1, 7);
      `checkd(s2, 2);
      `checkd(s4, 6);
      `checkd(s5, 7);
      `checkd(s6, 6);
      `checkd(s8, 8);
      `checkd(s9, 8'h11);
      `checkd(to.y, 8'(cyc - 1));
      `checkd(q_to, 8'(cyc - 1));
      `checkd(qf.y, 16'(cyc - 1));
      `checkd(qe.y, 8'(cyc - 1));
      `checkd(seen_q, 16'(cyc - 1));
      `checkd(cnt_ka, cyc);
      `checkd(ka.d, 8'(cyc));
      `checkd(ka.q, 8'(cyc - 1));
      `checkd(seen_fo, 8'd3);
    end
    if (cyc >= 2) `checkd(seen_k, 8'(cyc - 2));
    // Changed once, so the block runs once
    if (cyc == 2) begin
      data_x = 8'd5;
      exp_x = xa.y;
    end
    if (cyc > 2) `checkd(out_x, exp_x);
    if (cyc == 10) begin
      `checkd(cnt_kb, 7);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
