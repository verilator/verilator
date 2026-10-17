// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

interface tgt_if;
  int x, y, z, w;
endinterface

module t;
  logic [3:0] val[3];
  wire [3:0] #5 net[2];
  logic [1:0] idx1 = 0;
  logic [1:0] idx2 = 0;
  logic [0:0] idx3 = 0;
  int not_read = 0;
  event e;
  logic cat_a = 0, cat_b = 0, cat_c = 0, cat_d = 0, cat_e = 0, cat_f = 0, cat_g = 0, cat_h = 0;
  logic cat_i = 0, cat_j = 0, cat_k = 0, cat_l = 0, cat_m = 0, cat_n = 0, cat_o = 0, cat_p = 0;
  logic cap_x = 0;
  logic [7:0] fork_a = 0, fork_b = 0;
  string cat_log, fork_log;
  int dly_calls = 0, ones_calls = 0;
  process dly_proc, cap_proc;
  event cev;
  int pend_x, pend_z[3];
  string pend_log, pend_at4, pend_at6;
  int alw_src, alw_x, cls_x, cls_z[3];
  string alw_log, cls_log;
  tgt_if tgt_ifs[2] ();
  virtual tgt_if tgt_vifs[2], tgt_vaa[int], tgt_vwa[*];
  int tgt_a[2], tgt_c[2], tgt_d[2], tgt_keys[2], tgt_i;
  logic [7:0] tgt_v, tgt_p = 0;
  bit [7:0] tgt_sa[2], tgt_sb[2];
  string tgt_str;

  function automatic int dly();
    ++dly_calls;
    dly_proc = process::self();
    return 5;
  endfunction

  function automatic logic [1:0] ones();
    ++ones_calls;
    return 2'b11;
  endfunction

  function automatic int bit_of(logic [7:0] v, int i);
    return int'(v[i]);
  endfunction

  always @val
    $write(
        "[%0t] val[0]=%0d val[1]=%0d val[2]=%0d net[0]=%0d net[1]=%0d\n",
        $time,
        val[0],
        val[1],
        val[2],
        net[0],
        net[1]
    );

  assign {net[0], net[1]} = {val[1], 4'hf - val[1]};
  assign #4 val[1] = val[0];
  assign #6 val[2] = val[0];

  initial begin
    automatic time tm = $time;
    not_read = #1 1;
    if (tm != $time - 1) $stop;
  end

  // An intra-assignment timing control of an assignment to a concatenation is evaluated once,
  // after the value (IEEE 1800-2023 9.4.5), also in a fork
  initial begin
    {cat_a, cat_b} = #5 2'b11;
    cat_log = {cat_log, $sformatf("%0b%0b@%0t ", cat_a, cat_b, $time)};
    {cat_c, cat_d} <= #(dly()) 2'b11;
    {cat_g, cat_h} <= @(cev) 2'b11;
    {cat_m, cat_n} <= #0 2'b11;
    {cat_e, cat_f} = @(cev) 2'b11;
    cat_log = {cat_log, $sformatf("%0b%0b@%0t ", cat_e, cat_f, $time)};
  end
  initial begin
    {cat_o, cat_p} = #3 ones();
    cat_log = {cat_log, $sformatf("%0b%0b@%0t ", cat_o, cat_p, $time)};
  end
  initial #7 ->cev;
  initial begin
    fork
      begin
        {fork_a, fork_b} = #2 16'h0102;
        fork_log = $sformatf("%h@%0t", {fork_a, fork_b}, $time);
      end
      {cat_i, cat_j} <= #(dly()) 2'b11;
      {cat_k, cat_l} = ones();
    join_none
  end

  // The process executing an NBA evaluates its delay (IEEE 1800-2023 4.9.4)
  initial begin
    cap_proc = process::self();
    cap_x <= #(dly()) 1;
    `checkd(dly_proc == cap_proc, 1'b1)
  end

  // Each pending NBA keeps its own target and value, even if its process schedules more
  initial begin
    for (int i = 1; i <= 3; ++i) begin
      pend_x <= #5 i;
      #1;
    end
  end
  always @(pend_x) if ($time != 0) pend_log = {pend_log, $sformatf("%0d@%0t ", pend_x, $time)};
  initial begin
    for (int i = 0; i < 3; ++i) pend_z[i] <= #5 i + 1;
    #4 pend_at4 = $sformatf("%0d %0d %0d", pend_z[0], pend_z[1], pend_z[2]);
    #2 pend_at6 = $sformatf("%0d %0d %0d", pend_z[0], pend_z[1], pend_z[2]);
  end
  // Also in an always
  always @(alw_src) alw_x <= #5 alw_src;
  initial for (int i = 1; i <= 3; ++i) #1 alw_src = i;
  always @(alw_x) if ($time != 0) alw_log = {alw_log, $sformatf("%0d@%0t ", alw_x, $time)};
  // Also in a class method, which is not inlined, with or without a delay
  class Pend;
    static task run();
      for (int i = 1; i <= 3; ++i) begin
        cls_x <= #5 i;
        #1;
      end
      for (int i = 0; i < 3; ++i) cls_z[i] <= i + 1;
    endtask
  endclass
  initial Pend::run();
  always @(cls_x) if ($time != 0) cls_log = {cls_log, $sformatf("%0d@%0t ", cls_x, $time)};

  // The indices selecting the target are evaluated as the NBA executes, each as a whole, also the
  // functions they call, which select with their arguments. Also in the parts of a concatenation,
  // and through handles in arrays and in classes.
  class TgtHolder;
    virtual tgt_if vifs[2];
  endclass
  TgtHolder tgt_h = new;
  initial begin
    tgt_vifs[0] = tgt_ifs[0];
    tgt_vifs[1] = tgt_ifs[1];
    tgt_vaa[5] = tgt_ifs[0];
    tgt_vaa[6] = tgt_ifs[1];
    tgt_vwa[5] = tgt_ifs[0];
    tgt_vwa[6] = tgt_ifs[1];
    tgt_h.vifs = tgt_vifs;
    tgt_keys = '{5, 6};
    tgt_v = 8'b10;
    tgt_i = 1;
    tgt_a[bit_of(tgt_v, tgt_i)] <= #1 42;
    tgt_vifs[bit_of(tgt_v, tgt_i)].x <= #1 99;
    tgt_p[bit_of(tgt_v, tgt_i)*4+:4] <= #1 4'hf;
    {tgt_c[bit_of(tgt_v, tgt_i)], tgt_d[tgt_i]} <= #1 {32'd3, 32'd4};
    {>>{tgt_sa[tgt_i], tgt_sb[tgt_i]}} <= #1 16'h1234;
    tgt_vaa[tgt_keys[tgt_i]].y <= #1 10;
    tgt_vwa[tgt_keys[tgt_i]].z <= #1 20;
    tgt_h.vifs[bit_of(tgt_v, tgt_i)].w <= #1 30;
    tgt_i = 0;
  end

  initial begin
    #20;
    `checks(cat_log, "11@3 11@5 11@7 ")
    `checks(fork_log, "0102@2")
    `checkd({cat_c, cat_d, cat_g, cat_h, cat_i, cat_j, cat_k, cat_l, cat_m, cat_n, cap_x}, 11'h7ff)
    `checkd(ones_calls, 2)
    `checks(pend_log, "1@5 2@6 3@7 ")
    `checks(pend_at4, "0 0 0")
    `checks(pend_at6, "1 2 3")
    `checks(alw_log, "1@6 2@7 3@8 ")
    `checks(cls_log, "1@5 2@6 3@7 ")
    `checks($sformatf("%0d %0d %0d", cls_z[0], cls_z[1], cls_z[2]), "1 2 3")
    tgt_str = $sformatf("%0d %0d %h", tgt_a[0], tgt_a[1], tgt_p);
    `checks(tgt_str, "0 42 f0")
    tgt_str = $sformatf("%0d %0d %0d %0d", tgt_c[0], tgt_c[1], tgt_d[0], tgt_d[1]);
    `checks(tgt_str, "0 3 0 4")
    tgt_str = $sformatf("%h %h %h %h", tgt_sa[0], tgt_sa[1], tgt_sb[0], tgt_sb[1]);
    `checks(tgt_str, "00 12 00 34")
    tgt_str = $sformatf("%0d %0d %0d %0d", tgt_ifs[0].x, tgt_ifs[0].y, tgt_ifs[0].z, tgt_ifs[0].w);
    `checks(tgt_str, "0 0 0 0")
    tgt_str = $sformatf("%0d %0d %0d %0d", tgt_ifs[1].x, tgt_ifs[1].y, tgt_ifs[1].z, tgt_ifs[1].w);
    `checks(tgt_str, "99 10 20 30")
    // Last, as VCS evaluates the delay of an NBA to a concatenation for each part
    `checkd(dly_calls, 3)
  end

  always #10 begin  // always so we can use NBA
    val[0] = 1;
    #10 val[0] = 2;
    fork
      #5 val[0] = 3;
    join_none
    val[0] = #10 val[0] + 2;
    val[0] <= #10 val[idx1] + 2;
    fork
      begin
        #5 val[0] = 5;
        idx1 = 0;
        idx2 = 0;
        idx3 = 0;
        #40 ->e;
      end
    join_none
    idx1 = 2;
    idx2 = 3;
    idx3 = 1;
    val[idx1][idx2[idx3+:2]] = #20 1;
    @e val[0] = 8;
    fork
      begin
        #1 val[0] = 9;
        #2 ->e;
      end
    join_none
    val[0] = @e val[0] + 2;
    val[0] <= @e val[0] + 2;
    fork
      begin
        #1 val[0] = 11;
      end
    join_none
    #2 ->e;
    idx1 = 0;
    idx2 = 0;
    idx3 = 0;
    fork
      begin
        #2 idx1 = 2;
        idx2 = 3;
        idx3 = 1;
      end
    join_none
    #1 val[idx1[idx3+:2]][idx2] <= @e 1;
    #1 ->e;
    #1 $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
