// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Cast or real as the index of a dynamic array or queue element

module t (
  input clk
);
  initial begin
    typedef int index_t;
    typedef int dyn_t[];
    typedef dyn_t dyn_alias_t;
    typedef int queue_t[$];
    typedef queue_t queue_alias_t;
    automatic dyn_alias_t d = '{10, 11, 12, 13};
    automatic queue_alias_t q = '{20, 21, 22, 23};
    automatic bit [6:0] i;
    for (int k = 0; k < 4; k++) begin
      i = 7'(k + 4);
      `checkd(d[index_t'(i[1:0])], 10 + k);
      `checkd(d[2'(i)], 10 + k);
      `checkd(q[bit'(i) + 2'(i[1])], 20 + k[0] + k[1]);
      `checkd(q[$ - int'(i[1:0])], 23 - k);
    end
    for (int k = 0; k < 4; k++) begin
      i = 7'(k + 4);
      d[2'(i)] = 30 + k;
      q[int'(i[1:0])] = 40 + k;
    end
    `checkd(d[3], 33);
    `checkd(q[2], 42);
    for (int k = 0; k < 4; k++) begin
      i = 7'(k + 4);
      q[$ - index_t'(i[1:0])] = 50 + k;
      `checkd(q[$ - k], 50 + k);
    end
  end

  // Cast as a queue slice bound (bounds already finalized in V3WidthSel)
  initial begin
    automatic int q[$] = '{20, 21, 22, 23};
    automatic int s[$];
    automatic bit [6:0] i;
    for (int k = 0; k < 3; k++) begin
      i = 7'(k + 4);
      s = q[int'(i[1:0]):int'(i[1:0]) + 1];
      `checkd(s.size(), 2);
      `checkd(s[0], 20 + k);
      `checkd(s[1], 21 + k);
      s = q[2'(i):$];
      `checkd(s.size(), 4 - k);
      `checkd(s[0], 20 + k);
      s = q[0:$ - int'(i[1:0])];
      `checkd(s.size(), 4 - k);
      `checkd(s[$], 23 - k);
    end
  end

  // Real index, rounded as for an unpacked array (Verilator consistency check).
`ifdef VERILATOR
  initial begin
    automatic int u[4] = '{30, 31, 32, 33};
    automatic int d[] = '{10, 11, 12, 13};
    automatic int q[$] = '{20, 21, 22, 23};
    automatic real r;
    for (int k = 0; k < 3; k++) begin
      r = k + 0.6;
      // verilator lint_off REALCVT
      `checkd(u[r], 31 + k);
      `checkd(d[r], 11 + k);
      `checkd(q[r], 21 + k);
      // verilator lint_on REALCVT
    end
  end
`endif

  // Module-scope queue indexed through a function called from always_comb
  logic [3:0] mq[$];
  logic [7:0] id = 0;
  logic [3:0] vc;
  function automatic logic [3:0] pick(logic [7:0] i);
    return mq.size() == 0 ? 4'd0 : mq[int'(i) % mq.size()];
  endfunction
  always_comb vc = pick(id);

  int cyc = 0;
  logic [3:0] vals[3] = '{4'd4, 4'd8, 4'd5};
  always @(posedge clk) begin
    cyc <= cyc + 1;
    id <= id + 8'd29;
    `checkd(vc, mq.size() == 0 ? 4'd0 : vals[int'(id) % mq.size()]);
    if (cyc < 3) mq.push_back(vals[cyc]);
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
