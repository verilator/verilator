// DESCRIPTION: Verilator: NBAs that suspendable processes or forks execute several times in a
// time step, in an order not known statically, are performed in the order they executed
// (IEEE 1800-2023 4.6)
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef struct {
  int f;
  int g;
} pair_t;

module sub;
  int ref_v;
  logic [7:0] ref_p;
  int v;
  pair_t st;
  logic [7:0] p;

  // Until time 4, continue in the same time step, then suspend for an increasing time
  task automatic maybe_delay;
    int d = int'($time) / 4;
    if (d > 0) #(d);
  endtask

  // The NBAs at the end of the loop execute before the others in the same time step, until time
  // 4, so are overridden by them (issue #5485), as in the reference without them
  always begin
    ref_v <= 1;
    ref_p <= 8'hff;
    maybe_delay();
    ref_v <= 0;
    ref_p[3:0] <= 4'h0;
    #1;
  end
  always begin
    v <= 1;
    st.f <= 1;
    p <= 8'hff;
    maybe_delay();
    v <= 0;
    st.f <= 0;
    p[3:0] <= 4'h0;
    #1;
    v <= 1;
    st.f <= 1;
    p <= 8'hff;
  end
  always #1 begin
    `checkd(v, ref_v);
    `checkd(st.f, ref_v);
    `checkh(p, ref_p);
  end
endmodule

module t;
  sub s0 ();
  sub s1 ();

  // NBAs of two processes, the second one executing its NBA first, then waking the first one
  int ev_v;
  event ev;
  initial begin
    @ev;
    ev_v <= 2;
  end
  initial begin
    #1;
    ev_v <= 1;
    ->ev;
  end

  // NBAs of the branches of a fork, the second one executing first
  int fk_v;
  initial begin
    #1;
    fork
      begin
        #0;
        fk_v <= 1;
      end
      fk_v <= 2;
    join
  end

  // NBA in a loop, to bits selected by the loop
  logic [6:0] lp;
  int n;
  initial begin
    n = $urandom_range(5, 5);
    lp = '0;
    for (int i = 0; i < n; ++i) lp[i] <= 1'b1;
  end

  // NBA to a whole unpacked array
  logic [7:0] arr[0:3];
  logic [7:0] arr_src[0:3] = '{8'h11, 8'h22, 8'h33, 8'h44};
  initial #1 arr <= arr_src;

  initial begin
    #2;
    `checkd(ev_v, 2);
    `checkd(fk_v, 1);
    `checkh(lp, 7'b0011111);
    `checkh(arr[0], 8'h11);
    `checkh(arr[1], 8'h22);
    `checkh(arr[2], 8'h33);
    `checkh(arr[3], 8'h44);
    #20;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
