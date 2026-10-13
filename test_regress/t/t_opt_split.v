// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2003 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  integer cyc;
  initial cyc = 1;

  reg [15:0] m_din;

  // We expect all these blocks should split;
  // blocks that don't split should go in t_alw_nosplit.v

  reg [15:0] a_split_1, a_split_2;
  always @(  /*AS*/ m_din) begin
    a_split_1 = m_din;
    a_split_2 = m_din;
  end

  reg [15:0] d_split_1, d_split_2;
  always @(posedge clk) begin
    d_split_1 <= m_din;
    d_split_2 <= d_split_1;
    d_split_1 <= ~m_din;
  end

  reg [15:0] h_split_1;
  reg [15:0] h_split_2;
  always @(posedge clk) begin
    //      $write(" cyc = %x  m_din = %x\n", cyc, m_din);
    if (cyc > 2) begin
      if (m_din == 16'h0) begin
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
  end

  reg [15:0] l_split_1, l_split_2;
  always @(posedge clk) begin
    l_split_2 <= l_split_1;
    l_split_1 <= l_split_2 | m_din;
  end

  reg [15:0] p_split_1, p_split_2;
  always @(posedge clk) begin
    if (m_din != 16'h0) begin
      $write("");
      p_split_1 <= m_din;
    end
    p_split_2 <= ~m_din;
  end

  reg [15:0] q_split_1, q_split_2;
  always @(posedge clk) begin
    if (m_din[0]) q_split_1 <= 16'h1;
    else q_split_2 <= 16'h2;
  end

  reg [15:0] r_split_mem[0:3];
  reg [1:0] r_split_idx = 2'd0;
  always @(posedge clk) begin
    r_split_mem[r_split_idx] <= m_din;
    r_split_idx <= r_split_idx + 2'd1;
  end

  // Inlining this leaves only its comment behind, as its body is dead
  task automatic dead_task;
    automatic integer loc;
    begin
      loc = 1;
    end
  endtask

  integer seed = 1;
  reg [15:0] t_split_1, t_split_2;
  always @(posedge clk) begin
    // Nothing is left under the 'if', but the impure condition keeps its
    // vertex, so the condition alone is kept as a statement
    if ($random(seed) != 0) begin
      dead_task();
    end
    t_split_1 <= m_din;
    t_split_2 <= ~m_din;
  end

  reg [15:0] u_split_1, u_split_2;
  always @(posedge clk) begin
    // The same, but this condition reads only block inputs, so the vertex is
    // pruned and the 'if' goes altogether
    if (m_din[2]) begin
      dead_task();
    end
    u_split_1 <= m_din;
    u_split_2 <= ~m_din;
  end

  // The checker block won't split.
  always @(posedge clk) begin
    if (cyc != 0) begin
      cyc <= cyc + 1;
      if (cyc == 1) begin
        m_din <= 16'hfeed;
      end
      if (cyc == 3) begin
      end
      if (cyc == 4) begin
        m_din <= 16'he11e;
        //$write(" A %x %x\n", a_split_1, a_split_2);
        if (!(a_split_1 == 16'hfeed && a_split_2 == 16'hfeed)) $stop;
        if (!(d_split_1 == 16'h0112 && d_split_2 == 16'h0112)) $stop;
        if (!(h_split_1 == 16'hfeed && h_split_2 == 16'h0112)) $stop;
        if (!(p_split_1 == 16'hfeed && p_split_2 == 16'h0112)) $stop;
        if (!(q_split_1 == 16'h1)) $stop;
        if (!(r_split_idx == 2'd3)) $stop;
        if (!(r_split_mem[1] == 16'hfeed && r_split_mem[2] == 16'hfeed)) $stop;
        if (!(t_split_1 == 16'hfeed && t_split_2 == 16'h0112)) $stop;
        if (!(u_split_1 == 16'hfeed && u_split_2 == 16'h0112)) $stop;
      end
      if (cyc == 5) begin
        m_din <= 16'he22e;
        if (!(a_split_1 == 16'he11e && a_split_2 == 16'he11e)) $stop;
        if (!(d_split_1 == 16'h0112 && d_split_2 == 16'h0112)) $stop;
        if (!(h_split_1 == 16'hfeed && h_split_2 == 16'h0112)) $stop;
        if (!(p_split_1 == 16'hfeed && p_split_2 == 16'h0112)) $stop;
        if (!(q_split_1 == 16'h1)) $stop;
        if (!(r_split_idx == 2'd0 && r_split_mem[3] == 16'hfeed)) $stop;
        if (!(t_split_1 == 16'hfeed && t_split_2 == 16'h0112)) $stop;
        if (!(u_split_1 == 16'hfeed && u_split_2 == 16'h0112)) $stop;
      end
      if (cyc == 6) begin
        m_din <= 16'he33e;
        if (!(a_split_1 == 16'he22e && a_split_2 == 16'he22e)) $stop;
        if (!(d_split_1 == 16'h1ee1 && d_split_2 == 16'h0112)) $stop;
        if (!(h_split_1 == 16'he11e && h_split_2 == 16'h1ee1)) $stop;
        if (!(p_split_1 == 16'he11e && p_split_2 == 16'h1ee1)) $stop;
        if (!(q_split_1 == 16'h1 && q_split_2 == 16'h2)) $stop;
        if (!(r_split_idx == 2'd1 && r_split_mem[0] == 16'he11e)) $stop;
        if (!(t_split_1 == 16'he11e && t_split_2 == 16'h1ee1)) $stop;
        if (!(u_split_1 == 16'he11e && u_split_2 == 16'h1ee1)) $stop;
      end
      if (cyc == 7) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end  // always @ (posedge clk)

endmodule
