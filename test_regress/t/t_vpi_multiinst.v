// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Multi-instance and cross-scope VPI access under --public-flat-rw.
interface iface_t;
  logic [6:0] val;
  logic [6:0] derived;
  assign derived = val + 7'h1;
endinterface

// Port-alias helper target.
module sub (
    input logic [6:0] din,
    output logic [6:0] dout
);
  wire [6:0] din_copy;
  assign din_copy = din;
  assign dout = din_copy ^ 7'h0f;
endmodule

// Members driven by per-instance expressions in t.
interface iface2_t;
  logic [6:0] a;
  logic [6:0] b;
endinterface

// Non-inlined module, instanced once in each of t.p0 and t.p1: exercises
// per-instance storage rather than one table shared by the module class.
module child (
    input logic clk,
    input logic [7:0] din
);
  /*verilator no_inline_module*/
  logic [7:0] cy;
  assign cy = din ^ 8'hA5;
  logic [7:0] cflop = 8'h0;
  always_ff @(posedge clk) cflop <= din ^ 8'h5a;
endmodule

// bc is driven only by cross-scope assigns in module t; bd reads bc back
// from within this module's own scope.
module bcell;
  /*verilator no_inline_module*/
  logic [7:0] bc;
  logic [7:0] bd;
  assign bd = bc ^ 8'h33;
endmodule

module parent (
    input logic clk,
    input logic [7:0] din
);
  /*verilator no_inline_module*/
  child uc (
      .clk(clk),
      .din(din)
  );
  logic [7:0] py;
  assign py = uc.cy + 8'h03;
  // Cross-scope alias of a child flop.
  logic [7:0] xali;
  assign xali = uc.cflop;
endmodule

// Not inlined, so each instance keeps its own port storage.
module xsub (
    input logic [31:0] p,
    output logic [31:0] q
);
  /* verilator no_inline_module */
  assign q = p + 32'd7;
endmodule

// Same as xsub, but a separate module so its instances see only a flop-driven input
module xsubr (
    input logic [31:0] p,
    output logic [31:0] q
);
  /* verilator no_inline_module */
  assign q = p + 32'd7;
endmodule

module xsubre (
    input real p,
    output logic [31:0] q
);
  /* verilator no_inline_module */
  assign q = $rtoi(p) + 32'd7;
endmodule

module xsubse (
    input string p,
    output logic [31:0] q
);
  /* verilator no_inline_module */
  always_comb q = 32'(p.len());
endmodule

module t;

  logic clk;
  logic rst;

  initial begin
    clk = 1'b0;
    forever #5 clk = ~clk;
  end

  initial begin
    rst = 1'b1;
    @(posedge clk);
    @(negedge clk);
    rst = 1'b0;
  end

  // Cycle counter: one VPI-visible tick per clock, driving the stimulus
  // tables below and the harness puts.
  localparam logic [7:0] NumCycles = 8'd16;
  logic [7:0] cyc = 8'h0;

  always_ff @(posedge clk) begin
    if (rst) cyc <= 8'h0;
    else if (cyc < NumCycles) cyc <= cyc + 8'h1;
  end

  always @(posedge clk) begin
    if (!rst && cyc == NumCycles) begin
      t_vpi_dump_values();
      $write("*-* All Finished *-*\n");
      #1 $finish;
    end
  end

  import "DPI-C" context function void t_vpi_dump_values();
  import "DPI-C" context function void t_vpi_dump_cb(input string name);
  import "DPI-C" context function void t_vpi_dump_put_rw(
    input string name,
    input string value,
    input string flag = ""
  );

  initial begin
    t_vpi_dump_cb("t.cyc");
    t_vpi_dump_values();
  end
  always @(negedge clk) t_vpi_dump_values();
  // A put to one instance's flop leaves the other instance's alone
  always @(cyc) if (cyc == 8'd7) t_vpi_dump_put_rw("t.p0.uc.cflop", "3c");

  // Interface and submodule instances with differing inputs
  logic [6:0] ctr = 7'h0;

  iface_t if_a ();
  iface_t if_b ();
  iface_t if_c ();

  assign if_a.val = ctr + 7'h1;
  assign if_b.val = ctr ^ 7'h2a;
  assign if_c.val = 7'h55;

  logic [6:0] d0;
  logic [6:0] d1;
  sub u0 (
      .din(ctr & 7'h3c),
      .dout(d0)
  );
  sub u1 (
      .din(ctr | 7'h03),
      .dout(d1)
  );

  logic [6:0] observe = 7'h0;
  always_ff @(posedge clk) begin
    if (rst) begin
      ctr <= 7'h0;
      observe <= 7'h0;
    end
    else begin
      ctr <= ctr + 7'h3;
      observe <= if_a.derived ^ if_b.derived ^ if_c.derived ^ d0 ^ d1;
    end
  end

  // Interface instances whose members differ by expression
  logic [6:0] ctr2 = 7'h0;

  iface2_t if0 ();
  iface2_t if1 ();

  assign if0.a = ctr2;
  assign if1.a = ctr2 + 7'h1;
  assign if0.b = ~if0.a;
  assign if1.b = if1.a ^ 7'h55;

  logic [6:0] observe2 = 7'h0;
  always_ff @(posedge clk) begin
    if (rst) begin
      ctr2 <= 7'h0;
      observe2 <= 7'h0;
    end
    else begin
      ctr2 <= ctr2 + 7'h3;
      observe2 <= if0.b ^ if1.b;
    end
  end

  // Per-instance storage across the non-inlined parent/child modules (p0, p1),
  // plus a boundary alias of a child flop.
  function automatic logic [7:0] din0_of(input logic [7:0] cycle);
    case (cycle)
      8'd4: din0_of = 8'h00;
      8'd5: din0_of = 8'h13;
      8'd6: din0_of = 8'h2c;
      8'd7: din0_of = 8'h40;
      8'd8: din0_of = 8'h91;
      8'd9: din0_of = 8'ha5;
      8'd10: din0_of = 8'hff;
      default: din0_of = 8'h00;
    endcase
  endfunction

  logic [7:0] din0;
  logic [7:0] din1;
  assign din0 = din0_of(cyc);
  assign din1 = din0_of(cyc) + 8'h40;

  parent p0 (
      .clk(clk),
      .din(din0)
  );
  parent p1 (
      .clk(clk),
      .din(din1)
  );

  logic [7:0] acc_xscope = 8'h0;
  always_ff @(posedge clk) acc_xscope <= acc_xscope + p0.py + p1.py;
  logic [7:0] obs_xscope;
  assign obs_xscope = acc_xscope;

  // A combinational value and a flop, each passed to two instances of a non-inlined
  // module, and real and string flops passed the same way.
  logic [31:0] acc = 32'h0;
  logic [31:0] accn;
  logic [31:0] canon;
  logic [31:0] canonr = 32'h0;
  logic [31:0] qa, qb, qc, qd, qe, qf, qg, qh;

  function automatic logic [31:0] in2_of(input logic [7:0] cycle);
    case (cycle)
      8'd11: in2_of = 32'h00000001;
      8'd12: in2_of = 32'h00000010;
      8'd13: in2_of = 32'h00001234;
      8'd14: in2_of = 32'h0000007f;
      8'd15: in2_of = 32'h00000003;
      default: in2_of = 32'h0;
    endcase
  endfunction

  logic [31:0] in2;
  assign in2 = in2_of(cyc);

  always_comb accn = rst ? 32'd0 : acc + in2;

  always_ff @(posedge clk) begin
    acc <= accn;
    canonr <= accn ^ 32'ha5a5_a5a5;
  end

  always_comb canon = acc ^ 32'h5a5a_5a5a;

  real rcanonr;
  string scanonr;
  always_ff @(posedge clk) begin
    rcanonr <= $itor(accn) + 0.25;
    if (accn[0]) scanonr <= "odd";
    else scanonr <= "even";
  end

  xsub u_a (
      .p(canon),
      .q(qa)
  );
  xsub u_b (
      .p(canon),
      .q(qb)
  );
  xsubr u_c (
      .p(canonr),
      .q(qc)
  );
  xsubr u_d (
      .p(canonr),
      .q(qd)
  );
  xsubre u_e (
      .p(rcanonr),
      .q(qe)
  );
  xsubre u_f (
      .p(rcanonr),
      .q(qf)
  );
  xsubse u_g (
      .p(scanonr),
      .q(qg)
  );
  xsubse u_h (
      .p(scanonr),
      .q(qh)
  );

  logic [31:0] obs_canon;
  assign obs_canon = qa ^ qb ^ qc ^ qd ^ qe ^ qf ^ qg ^ qh;

  // Boundary comb copy: bc0.bc/bc1.bc are driven only by the cross-scope
  // assigns below; bd reads bc back from within bcell's own scope.
  logic [7:0] bflop0 = 8'h0;
  logic [7:0] bflop1 = 8'h0;
  always_ff @(posedge clk) begin
    bflop0 <= din0 ^ 8'ha5;
    bflop1 <= din1 ^ 8'ha5;
  end

  bcell bc0 ();
  bcell bc1 ();
  assign bc0.bc = bflop0;
  assign bc1.bc = bflop1;

endmodule
