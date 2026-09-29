// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Flat-rw VPI coverage of combinational shapes: partial and multi-dimensional
// coverage, real/string aliases, forceable signals, multidriven ports,
// a public_flat_rd pin, and a chandle variable.
module sub_drv (
    output wire [7:0] y,
    input wire [7:0] x
);
  assign y = x;
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

  localparam logic [7:0] NumCycles = 8'd20;
  logic [7:0] cyc = 8'h0;

  always_ff @(posedge clk) begin
    if (rst) cyc <= 8'h0;
    else if (cyc < NumCycles) cyc <= cyc + 8'h1;
  end

  always @(posedge clk) begin
    if (!rst && cyc == NumCycles) begin
      $write("*-* All Finished *-*\n");
      #1 $finish;
    end
  end

  import "DPI-C" context function void t_vpi_dump_values();
  import "DPI-C" context function void t_vpi_dump_skip(input string name);
  import "DPI-C" context function void t_vpi_dump_cb(input string name);
  import "DPI-C" context function string t_vpi_dump_get(input string name);
  import "DPI-C" context function void t_vpi_dump_put_rw(
    input string name,
    input string value,
    input string flag = ""
  );

  // Multiply-driven and impure signals resolve by how the model was optimised, so are not
  // dumped
  initial begin
    t_vpi_dump_skip("t.vec");
    t_vpi_dump_skip("t.obs_impureidx");
    t_vpi_dump_skip("t.w");
    t_vpi_dump_skip("t.u_wdrv.y");
    t_vpi_dump_cb("t.cyc");
    t_vpi_dump_values();
  end
  always @(clk) t_vpi_dump_values();
  always @(cyc) begin
    case (cyc)
      8'd8: t_vpi_dump_put_rw("t.orphan", "2a");
      // No vpi_put_value format for chandle; Questa rejects, and this golden records the
      // put being accepted
      8'd9: t_vpi_dump_put_rw("t.handle", "2a");
      8'd14: t_vpi_dump_put_rw("t.frc", "55", "force");
      8'd16: t_vpi_dump_put_rw("t.frc", "55", "release");
      default: ;
    endcase
  end

  // Stimulus tables driving 'a'/'b' at specific cycles; 0 elsewhere.
  function automatic logic [7:0] a_of(input logic [7:0] cycle);
    case (cycle)
      8'd4: a_of = 8'h3c;
      8'd5: a_of = 8'h2b;
      8'd6: a_of = 8'h5a;
      default: a_of = 8'h00;
    endcase
  endfunction

  function automatic logic [7:0] b_of(input logic [7:0] cycle);
    case (cycle)
      8'd5: b_of = 8'h74;
      8'd6: b_of = 8'h33;
      default: b_of = 8'h00;
    endcase
  endfunction

  function automatic logic frc2force_of(input logic [7:0] cycle);
    frc2force_of = (cycle == 8'd10 || cycle == 8'd11);
  endfunction

  logic [7:0] a;
  logic [7:0] b;
  logic [3:0] data;
  logic frc2_force;
  assign a = a_of(cyc);
  assign b = b_of(cyc);
  assign data = 4'h5;
  assign frc2_force = frc2force_of(cyc);

  // An impure bit-select index is not a compile-time constant, so each read
  // must re-evaluate the current index. 'obs_impureidx' is a second, independent
  // read path to the same value: VPI must read both the same.
  logic [31:0] seedv = 32'h0;
  logic [7:0] vec;
  logic [7:0] obs_impureidx;
  always_comb vec[($urandom(seedv)&3)+:4] = data;
  assign obs_impureidx = vec;
  // An initial process, as a --threads model resumes those on the thread VPI needs
  initial begin
    forever begin
      @(negedge clk);
      `checks(t_vpi_dump_get("t.vec"), t_vpi_dump_get("t.obs_impureidx"));
    end
  end

  // 'out' is assembled from two independent bit-slice writes off 'keep'.
  logic [7:0] keep = 8'h0;
  logic [7:0] out;
  assign out[3:0] = keep[3:0];
  assign out[7:4] = keep[7:4] ^ 4'hf;
  always_ff @(posedge clk) begin
    if (rst) keep <= 8'h0;
    else keep <= keep + 8'h11;
  end

  // Basic and aggregate dtypes
  typedef enum logic [1:0] {
    A,
    B,
    C,
    D
  } e_t;
  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } ps_t;
  typedef struct {
    logic [7:0] a;
    logic [7:0] b;
  } us_t;

  real r_comb;
  always_comb r_comb = 1.5;
  integer i_comb;
  always_comb i_comb = integer'(a) + 1;
  e_t en_comb;
  always_comb en_comb = e_t'(a[1:0]);
  string s_var;
  always_comb s_var = "hi";
  logic [6:0] v_comb;
  always_comb v_comb = a[6:0] ^ 7'h5;
  string s_fmt;
  always_comb s_fmt = $sformatf("v%0d", a);  // impure

  ps_t ps_comb;
  always_comb begin
    ps_comb.hi = a[7:4];
    ps_comb.lo = a[3:0];
  end
  logic [3:0][7:0] pa_comb;
  always_comb pa_comb = {a, a ^ 8'hff, a + 8'd1, a - 8'd1};

  us_t us_comb;
  always_comb begin
    us_comb.a = a;
    us_comb.b = ~a;
  end
  logic [7:0] mem[0:3];
  always_comb begin
    mem[0] = a;
    mem[1] = a + 1;
    mem[2] = a + 2;
    mem[3] = a + 3;
  end

  // Only element 0 of 'mem_part' is ever driven; elements 1-3 stay undriven.
  logic [7:0] mem_part[0:3];
  always_comb mem_part[0] = a ^ 8'h27;

  // Element coverage over unequal, mixed-direction, non-zero-based dims, with one
  // element assembled from two adjacent packed slices.
  logic [15:0] md_full[3:1][0:1];
  always_comb begin
    md_full[1][0][7:0] = a;
    md_full[1][0][15:8] = ~a;
    md_full[1][1] = {a, 8'h11};
    md_full[2][0] = {a, 8'h22};
    md_full[2][1] = {a, 8'h33};
    md_full[3][0] = {a, 8'h44};
    md_full[3][1] = {a, 8'h55};
  end

  // Same shape, but one element's high byte is left undriven.
  logic [15:0] md_gap[0:1][2:0];
  always_comb begin
    md_gap[0][0][7:0] = a;
    md_gap[0][1] = {a, 8'h11};
    md_gap[0][2] = {a, 8'h22};
    md_gap[1][0] = {a, 8'h33};
    md_gap[1][1] = {a, 8'h44};
    md_gap[1][2] = {a, 8'h55};
  end

  logic [7:0] obs_dtypes;
  assign obs_dtypes = {1'b0, v_comb} ^ i_comb[7:0] ^ mem[0] ^ ps_comb ^ pa_comb[0] ^ us_comb.a
                     ^ {6'b0, en_comb} ^ {7'b0, s_fmt.len() != 0};

  // Full coverage over differing select depths: one element write, one whole-row write.
  logic [7:0] mixdep[0:1][0:1];
  always_comb begin
    mixdep[0][0] = a;
    mixdep[0][1] = b;
    mixdep[1] = '{a ^ 8'hff, b ^ 8'hff};
  end

  // Real and string values read normally through a continuous copy.
  real rc_src;
  real rc_alias;
  string sc_src;
  string sc_alias;
  always_ff @(posedge clk) begin
    rc_src <= $itor(a) + 0.5;
    if (a[0]) sc_src <= "odd";
    else sc_src <= "even";
  end
  always_comb rc_alias = rc_src;
  always_comb sc_alias = sc_src;

  real rf_mid;
  string sf_mid;
  always_comb rf_mid = r_comb;
  always_comb sf_mid = s_var;

  // 'wide' has more packed dimensions than 'narrow'; VPI must read both correctly.
  logic [7:0] ctr = 8'h0;
  logic [1:0][1:0][1:0][1:0] wide;
  logic [7:0] narrow;

  assign wide = {ctr, ~ctr};
  assign narrow = ctr + 8'h1;

  always_ff @(posedge clk) begin
    if (rst) ctr <= 8'h0;
    else ctr <= ctr + 8'h3;
  end

  // A chandle variable, written only by the initial block; a VPI put is the only
  // other way to change it.
  chandle handle;
  initial handle = null;

  // 'comb_inc' is combinational; 'orphan' has no driver at all, so a
  // VPI put is its only source; 'p' is assembled from two independent writes under
  // a split_var pragma that keeps it as one word.
  logic [7:0] comb_inc;
  assign comb_inc = a + 8'd1;

  logic [7:0] orphan;

  // verilator lint_off SPLITVAR
  logic [7:0] p  /*verilator split_var*/;
  // verilator lint_on SPLITVAR
  assign p[3:0] = a[3:0];
  always_comb p[7:4] = a[7:4];

  // 'w' is a net with two continuous drivers (IEEE 1800-2023 6.5): one from the
  // submodule instance, one directly. A port keeps V3Tristate from collapsing them
  // to one driver. 'r' has a single driver.
  // verilator lint_off MULTIDRIVEN
  wire [7:0] w;
  sub_drv u_wdrv (
      .y(w),
      .x(b)
  );
  assign w = a;
  // verilator lint_on MULTIDRIVEN

  logic [7:0] r;
  assign r = a & b;

  // Forceable signals
  logic [6:0] keep_frc = 7'h0;
  logic [6:0] frc  /* verilator forceable */;
  logic [6:0] frc2;

  assign frc = keep_frc + 7'h11;
  assign frc2 = keep_frc + 7'h22;

  always_ff @(posedge clk) begin
    if (rst) keep_frc <= 7'h0;
    else keep_frc <= keep_frc + 7'h3;
  end

  // 'frc2' has no forceable metacomment but is forced by SV force/release.
  always @(posedge clk) begin
    if (frc2_force) force frc2 = 7'h55;
    else release frc2;
  end

  // An explicit public_flat_rd pin; --public-flat-rw still makes it writable, so no put is
  // made here
  logic [7:0] rdpin  /*verilator public_flat_rd*/ = 8'h0;
  always_ff @(posedge clk) rdpin <= a ^ 8'h6d;

endmodule
