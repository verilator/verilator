// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2018 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc = 1;
  always @(posedge clk) cyc <= cyc + 1;

  reg [15:0] m_din;

  // We expect none of these blocks to split.
  // Blocks that can split should go in t_alw_split.v instead.

  reg [15:0] b_split_1, b_split_2;
  always @(  /*AS*/ m_din) begin
    b_split_1 = m_din;
    b_split_2 = b_split_1;
  end

  reg [15:0] c_split_1, c_split_2;
  always @(  /*AS*/ m_din) begin
    c_split_1 = m_din;
    c_split_2 = c_split_1;
    c_split_1 = ~m_din;
  end

  always @(posedge clk) begin
    $write(" foo %x", m_din);
    $write(" bar %x\n", m_din);
  end

  reg [15:0] e_split_1, e_split_2;
  always @(posedge clk) begin
    e_split_1 = m_din;
    e_split_2 = e_split_1;
  end

  reg [15:0] f_split_1, f_split_2;
  always @(posedge clk) begin
    f_split_2 = f_split_1;
    f_split_1 = m_din;
  end

  function logic [15:0] sideeffect_func(logic [15:0] v);
    /*verilator no_inline_task */
    $display("[%0t] sideeffect_func() is called", $time);
    return ~v;
  endfunction
  reg [15:0] m_split_1 = 0;
  reg [15:0] m_split_2 = 0;
  always @(posedge clk) begin
    if (sideeffect_func(m_split_1) != 16'b0) begin
      m_split_1 <= m_din;
    end
    else begin
      m_split_2 <= m_din;
    end
  end


  reg [15:0] z_split_1, z_split_2;
  always @(posedge clk) begin
    z_split_1 <= 0;
    z_split_1 <= ~m_din;
  end
  always @(posedge clk) begin
    z_split_2 <= 0;
    z_split_2 <= z_split_1;
  end

  reg [15:0] h_split_1;
  reg [15:0] h_split_2;
  reg [15:0] h_foo;
  always @(posedge clk) begin
    //      $write(" cyc = %x  m_din = %x\n", cyc, m_din);
    h_foo = m_din;
    if (cyc > 2) begin
      // This conditional depends on non-primary-input foo.
      // Its dependency on foo should not be pruned. As a result,
      // the dependencies of h_split_1 and h_split_2 on this
      // conditional will also not be pruned, making them all
      // weakly connected such that they'll end up in the same graph
      // and we can't split.
      if (h_foo == 16'h0) begin
        h_split_1 <= 16'h0;
        h_split_2 <= 16'h0;
      end
      else begin
        h_split_1 <= m_din;
        h_split_2 <= ~m_din;
      end
    end
    else begin
      h_split_1 <= 16'h0;
      h_split_2 <= 16'h0;
    end
  end  // always @ (posedge clk)

  reg [15:0] n_split_1, n_split_2;
  always @(posedge clk) begin
    @(negedge clk);
    n_split_1 <= m_din;
    n_split_2 <= ~m_din;
  end

  reg [15:0] o_split_1, o_split_2;
  reg [15:0] o_cnt;
  always @(posedge clk) begin
    o_cnt = 16'h0;
    while (o_cnt < m_din) begin
      if (m_din[0]) break;
      o_cnt = o_cnt + 16'h1;
    end
    o_split_1 <= m_din;
    if (m_din[1]) o_split_2 <= ~m_din;
  end

  reg [15:0] p_split_1;
  reg [15:0] p_cnt;
  always @(posedge clk) begin : pblk
    p_split_1 <= m_din;
    p_cnt = 16'h0;
    while (p_cnt < m_din) begin
      @(negedge clk);
      disable pblk;
    end
  end

  // The same constructs, but outside of any always block
  function automatic [15:0] fret(input [15:0] a);
    fret = 16'h0;
    if (a[0]) return 16'hbeef;
    fret = a;
  endfunction
  reg [15:0] q_init_1, q_init_2, q_init_3;
  reg [15:0] q_cnt;
  initial begin : qblk
    if (m_din == 16'h0) q_init_1 = 16'h1;
    q_init_1 <= 16'h2;
    q_init_2 = fret(m_din | 16'h1);
    q_cnt = 16'h0;
    while (q_cnt < (m_din | 16'h1)) begin
      q_cnt = q_cnt + 16'h1;
      q_init_3 = q_cnt;
      disable qblk;
    end
  end

  always @(posedge clk) begin
    if (cyc == 1) begin
      m_din <= 16'hfeed;
    end
    if (cyc == 4) begin
      m_din <= 16'he11e;
      if (!(b_split_1 == 16'hfeed && b_split_2 == 16'hfeed)) $stop;
      if (!(c_split_1 == 16'h0112 && c_split_2 == 16'hfeed)) $stop;
      if (!(e_split_1 == 16'hfeed && e_split_2 == 16'hfeed)) $stop;
      if (!(f_split_1 == 16'hfeed && f_split_2 == 16'hfeed)) $stop;
      if (!(m_split_1 == 16'hfeed && m_split_2 == 16'h0000)) $stop;
      if (!(z_split_1 == 16'h0112 && z_split_2 == 16'h0112)) $stop;
      if (!(n_split_1 == 16'hfeed && n_split_2 == 16'h0112)) $stop;
      if (!(o_split_1 == 16'hfeed)) $stop;
      if (!(p_split_1 == 16'hfeed)) $stop;
      if (!(q_init_1 == 16'h2 && q_init_2 == 16'hbeef && q_init_3 == 16'h1)) $stop;
    end
    if (cyc == 5) begin
      m_din <= 16'he22e;
      if (!(b_split_1 == 16'he11e && b_split_2 == 16'he11e)) $stop;
      if (!(c_split_1 == 16'h1ee1 && c_split_2 == 16'he11e)) $stop;
      // Two valid orderings, as we don't know which posedge clk gets evaled first
      if (!(e_split_1==16'hfeed && e_split_2==16'hfeed) && !(e_split_1==16'he11e && e_split_2==16'he11e))
        $stop;
      if (!(f_split_1==16'hfeed && f_split_2==16'hfeed) && !(f_split_1==16'he11e && f_split_2==16'hfeed))
        $stop;
      if (!(m_split_1 == 16'hfeed && m_split_2 == 16'h0000)) $stop;
      if (!(z_split_1 == 16'h0112 && z_split_2 == 16'h0112)) $stop;
      if (!(n_split_1 == 16'he11e && n_split_2 == 16'h1ee1)) $stop;
      if (!(o_split_1 == 16'hfeed)) $stop;
      if (!(p_split_1 == 16'hfeed)) $stop;
    end
    if (cyc == 6) begin
      m_din <= 16'he33e;
      if (!(b_split_1 == 16'he22e && b_split_2 == 16'he22e)) $stop;
      if (!(c_split_1 == 16'h1dd1 && c_split_2 == 16'he22e)) $stop;
      // Two valid orderings, as we don't know which posedge clk gets evaled first
      if (!(e_split_1==16'he11e && e_split_2==16'he11e) && !(e_split_1==16'he22e && e_split_2==16'he22e))
        $stop;
      if (!(f_split_1==16'he11e && f_split_2==16'hfeed) && !(f_split_1==16'he22e && f_split_2==16'he11e))
        $stop;
      if (!(m_split_1 == 16'he11e && m_split_2 == 16'h0000)) $stop;
      if (!(z_split_1 == 16'h1ee1 && z_split_2 == 16'h0112)) $stop;
      if (!(n_split_1 == 16'he22e && n_split_2 == 16'h1dd1)) $stop;
      if (!(o_split_1 == 16'he11e && o_split_2 == 16'h1ee1)) $stop;
      if (!(p_split_1 == 16'he11e)) $stop;
    end
    if (cyc == 7) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
