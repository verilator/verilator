// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A partition when compiled with --hierarchical
module part (
    input clk,
    input [7:0] in,
    output logic [7:0] out
);
  /*verilator hier_block*/
  logic [7:0] part_q;
  always_ff @(posedge clk) begin
    part_q <= in;
    out <= part_q;
  end
endmodule

package pkg;
  int pkg_var;
endpackage

interface ifc;
  logic [7:0] data;
endinterface

module sub #(
    parameter int WIDTH = 8
) (
    input clk,
    ifc i
);
  // Constants are located via the global table
  localparam logic [7:0] MAGIC = 8'h5a;
  enum logic [1:0] {
    IDLE,
    RUN,
    DONE
  } state;
  enum bit [2:0] {
    RED,
    GREEN
  } color;
  enum {
    LOW,
    HIGH
  } level;

  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } pair;
  union packed signed {
    logic [7:0] s;
    logic [7:0] u;
  } word;
  struct {
    int count;
    logic flag;
  } info;
  logic [7:0] mem[0:3];
  struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } pairs[2];
  logic signed sbit;
  byte sbyte;
  int unsigned uint;
  logic signed [7:0] svec;
  logic signed [3:0][7:0] sarr;
  logic signed [7:0] smem[0:1];
  real rval;
  time tval;
  event ev;
  chandle ch;
  // Ascending ranges are intentional, to check their indices
  // verilator lint_off ASCRANGE
  logic [1:3][4:1] pmd;
  bit [0:7] asc;
  logic [3:2] umd[1:2][5:3];
  logic [2:1][0:1] mix[4:3];
  // verilator lint_on ASCRANGE
  int cnt3[3];
  // Not traced, but still enumerated
  // verilator tracing_off
  logic [7:0] untraced;
  // verilator tracing_on

  int cnt = 0;
  always_ff @(posedge clk) begin : blk
    int nxt;
    nxt = cnt + 1;
    cnt <= nxt;
  end
  assign i.data = cnt[7:0];
  wire [7:0] wsum = cnt[7:0] + MAGIC;

  // Reference every variable, so none are removed. The model is never finalized.
  final begin
    $display("%p", state);
    $display("%p", color);
    $display("%p", level);
    $display("%p", pair);
    $display("%p", word);
    $display("%p", info);
    $display("%p", mem);
    $display("%p", pairs);
    $display("%p", sbit);
    $display("%p", sbyte);
    $display("%p", uint);
    $display("%p", svec);
    $display("%p", sarr);
    $display("%p", smem);
    $display("%p", rval);
    $display("%p", tval);
    $display("%p", ev.triggered);
    $display("%p", ch == null);
    $display("%p", pmd);
    $display("%p", asc);
    $display("%p", umd);
    $display("%p", mix);
    $display("%p", cnt3);
    $display("%p", untraced);
    $display("%p", WIDTH);
    $display("%p", MAGIC);
    $display("%p", wsum);
  end
endmodule

module t (
    input clk
);
  ifc i ();
  sub u_sub (
      .clk(clk),
      .i(i)
  );
  // The interface is declared after the instance referencing it
  sub u_late (
      .clk(clk),
      .i(late_i)
  );
  ifc late_i ();

  logic [7:0] q0;
  part u_part (
      .clk(clk),
      .in(i.data),
      .out(q0)
  );

  for (genvar g = 0; g < 2; ++g) begin : gen
    localparam int OFFSET = g + 1;
    logic [7:0] q;
    wire [7:0] qoff = q + 8'(OFFSET);
    part u_part (
        .clk(clk),
        .in(i.data + 8'(g)),
        .out(q)
    );
  end

  // Static, so its variable is described in its own level
  task tick();
    int ticks;
    ticks = ticks + 1;
    pkg::pkg_var = ticks;
  endtask

  always_ff @(posedge clk) tick();

  initial begin : init
    int ivar;
    ivar = 1;
    fork : frk
      int fvar;
      fvar = ivar;
    join
  end
endmodule
