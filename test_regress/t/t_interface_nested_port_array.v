// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Nested interface ports through interface arrays
// Similar structure to t_interface_nested_port.v, but with interface arrays.

interface l0_if #(
    parameter int W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
endinterface

interface l1_if #(
    parameter int W = 8,
    parameter int L0A_W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
  l0_if #(L0A_W) l0a[1:0] ();  // arrayed passthrough
  l0_if l0b ();  // default
endinterface

interface l2_if #(
    parameter int W = 8,
    parameter int L0A_W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
  l1_if #(W * 2, L0A_W) l1[1:0] ();  // derived
endinterface

interface l3_if #(
    parameter int W = 8,
    parameter int L0A_W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
  l2_if #(W * 2, L0A_W) l2[1:0] ();  // arrayed
endinterface

module l0_handler #(
    parameter int W = 8
) (
    input logic clk,
    l0_if#(W) l0,
    output logic [W-1:0] dout
);
  always_ff @(posedge clk) l0.dut_out <= l0.tb_in ^ W'('1);
  assign dout = l0.dut_out;
endmodule

module l1_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l1_if#(W, L0A_W) l1,
    output logic [W-1:0] l1_dout,
    output logic [L0A_W-1:0] l0a0_dout,
    output logic [L0A_W-1:0] l0a1_dout,
    output logic [7:0] l0b_dout
);
  always_ff @(posedge clk) l1.dut_out <= l1.tb_in ^ W'('1);
  assign l1_dout = l1.dut_out;
  l0_handler #(L0A_W) m_l0a0 (
      .clk(clk),
      .l0(l1.l0a[0]),
      .dout(l0a0_dout)
  );
  l0_handler #(L0A_W) m_l0a1 (
      .clk(clk),
      .l0(l1.l0a[1]),
      .dout(l0a1_dout)
  );
  l0_handler #(8) m_l0b (
      .clk(clk),
      .l0(l1.l0b),
      .dout(l0b_dout)
  );
endmodule

module l2_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l2_if#(W, L0A_W) l2,
    output logic [W-1:0] l2_dout,
    output logic [W*2-1:0] l1_0_dout,
    output logic [L0A_W-1:0] l0a0_0_dout,
    output logic [L0A_W-1:0] l0a1_1_dout,
    output logic [7:0] l0b_1_dout
);
  always_ff @(posedge clk) l2.dut_out <= l2.tb_in ^ W'('1);
  assign l2_dout = l2.dut_out;
  l1_handler #(W * 2, L0A_W) m_l1_0 (
      .clk(clk),
      .l1(l2.l1[0]),
      .l1_dout(l1_0_dout),
      .l0a0_dout(l0a0_0_dout),
      .l0a1_dout(),
      .l0b_dout()
  );
  l1_handler #(W * 2, L0A_W) m_l1_1 (
      .clk(clk),
      .l1(l2.l1[1]),
      .l1_dout(),
      .l0a0_dout(),
      .l0a1_dout(l0a1_1_dout),
      .l0b_dout(l0b_1_dout)
  );
endmodule

module l2_array_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l2_if#(W, L0A_W) l2s[1:0],
    output logic [W-1:0] l2a_dout,
    output logic [W*2-1:0] l2a_l1_0_dout,
    output logic [L0A_W-1:0] l2a_l0a0_0_dout,
    output logic [L0A_W-1:0] l2a_l0a1_1_dout,
    output logic [7:0] l2a_l0b_1_dout,
    output logic [W-1:0] l2b_dout,
    output logic [W*2-1:0] l2b_l1_0_dout,
    output logic [L0A_W-1:0] l2b_l0a0_0_dout,
    output logic [L0A_W-1:0] l2b_l0a1_1_dout,
    output logic [7:0] l2b_l0b_1_dout
);
  l2_handler #(W, L0A_W) m_l2a (
      .clk(clk),
      .l2(l2s[0]),
      .l2_dout(l2a_dout),
      .l1_0_dout(l2a_l1_0_dout),
      .l0a0_0_dout(l2a_l0a0_0_dout),
      .l0a1_1_dout(l2a_l0a1_1_dout),
      .l0b_1_dout(l2a_l0b_1_dout)
  );
  l2_handler #(W, L0A_W) m_l2b (
      .clk(clk),
      .l2(l2s[1]),
      .l2_dout(l2b_dout),
      .l1_0_dout(l2b_l1_0_dout),
      .l0a0_0_dout(l2b_l0a0_0_dout),
      .l0a1_1_dout(l2b_l0a1_1_dout),
      .l0b_1_dout(l2b_l0b_1_dout)
  );
endmodule

module l3_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l3_if#(W, L0A_W) l3,
    output logic [W-1:0] l3_dout,
    output logic [W*2-1:0] l2a_dout,
    output logic [W*4-1:0] l2a_l1_0_dout,
    output logic [L0A_W-1:0] l2a_l0a0_0_dout,
    output logic [L0A_W-1:0] l2a_l0a1_1_dout,
    output logic [7:0] l2a_l0b_1_dout,
    output logic [W*2-1:0] l2b_dout,
    output logic [W*4-1:0] l2b_l1_0_dout,
    output logic [L0A_W-1:0] l2b_l0a0_0_dout,
    output logic [L0A_W-1:0] l2b_l0a1_1_dout,
    output logic [7:0] l2b_l0b_1_dout
);
  always_ff @(posedge clk) l3.dut_out <= l3.tb_in ^ W'('1);
  assign l3_dout = l3.dut_out;
  l2_array_handler #(W * 2, L0A_W) m_l2 (
      .clk(clk),
      .l2s(l3.l2),
      .l2a_dout(l2a_dout),
      .l2a_l1_0_dout(l2a_l1_0_dout),
      .l2a_l0a0_0_dout(l2a_l0a0_0_dout),
      .l2a_l0a1_1_dout(l2a_l0a1_1_dout),
      .l2a_l0b_1_dout(l2a_l0b_1_dout),
      .l2b_dout(l2b_dout),
      .l2b_l1_0_dout(l2b_l1_0_dout),
      .l2b_l0a0_0_dout(l2b_l0a0_0_dout),
      .l2b_l0a1_1_dout(l2b_l0a1_1_dout),
      .l2b_l0b_1_dout(l2b_l0b_1_dout)
  );
endmodule

module t;
  logic clk = 0;
  int cyc = 0;

  localparam int TOP_W = 4;
  localparam int L0A_W = 12;

  l3_if #(TOP_W, L0A_W) inst ();

  logic [TOP_W-1:0] l3_dout;
  logic [TOP_W*2-1:0] l2a_dout;
  logic [TOP_W*4-1:0] l2a_l1_0_dout;
  logic [L0A_W-1:0] l2a_l0a0_0_dout;
  logic [L0A_W-1:0] l2a_l0a1_1_dout;
  logic [7:0] l2a_l0b_1_dout;
  logic [TOP_W*2-1:0] l2b_dout;
  logic [TOP_W*4-1:0] l2b_l1_0_dout;
  logic [L0A_W-1:0] l2b_l0a0_0_dout;
  logic [L0A_W-1:0] l2b_l0a1_1_dout;
  logic [7:0] l2b_l0b_1_dout;

  l3_handler #(TOP_W, L0A_W) m_l3 (
      .clk(clk),
      .l3(inst),
      .l3_dout(l3_dout),
      .l2a_dout(l2a_dout),
      .l2a_l1_0_dout(l2a_l1_0_dout),
      .l2a_l0a0_0_dout(l2a_l0a0_0_dout),
      .l2a_l0a1_1_dout(l2a_l0a1_1_dout),
      .l2a_l0b_1_dout(l2a_l0b_1_dout),
      .l2b_dout(l2b_dout),
      .l2b_l1_0_dout(l2b_l1_0_dout),
      .l2b_l0a0_0_dout(l2b_l0a0_0_dout),
      .l2b_l0a1_1_dout(l2b_l0a1_1_dout),
      .l2b_l0b_1_dout(l2b_l0b_1_dout)
  );

  always #5 clk = ~clk;

  always_ff @(posedge clk) begin
    inst.tb_in <= cyc[TOP_W-1:0];

    inst.l2[0].tb_in <= cyc[TOP_W*2-1:0] + (TOP_W * 2)'(1);
    inst.l2[0].l1[0].tb_in <= cyc[TOP_W*4-1:0] + (TOP_W * 4)'(2);
    inst.l2[0].l1[0].l0a[0].tb_in <= cyc[L0A_W-1:0] + L0A_W'(3);
    inst.l2[0].l1[1].l0a[1].tb_in <= cyc[L0A_W-1:0] + L0A_W'(4);
    inst.l2[0].l1[1].l0b.tb_in <= cyc[7:0] + 8'd5;

    inst.l2[1].tb_in <= cyc[TOP_W*2-1:0] + (TOP_W * 2)'(6);
    inst.l2[1].l1[0].tb_in <= cyc[TOP_W*4-1:0] + (TOP_W * 4)'(7);
    inst.l2[1].l1[0].l0a[0].tb_in <= cyc[L0A_W-1:0] + L0A_W'(8);
    inst.l2[1].l1[1].l0a[1].tb_in <= cyc[L0A_W-1:0] + L0A_W'(9);
    inst.l2[1].l1[1].l0b.tb_in <= cyc[7:0] + 8'd10;
  end

  logic [TOP_W-1:0] exp_l3_dout;
  logic [TOP_W*2-1:0] exp_l2a_dout;
  logic [TOP_W*4-1:0] exp_l2a_l1_0_dout;
  logic [L0A_W-1:0] exp_l2a_l0a0_0_dout;
  logic [L0A_W-1:0] exp_l2a_l0a1_1_dout;
  logic [7:0] exp_l2a_l0b_1_dout;
  logic [TOP_W*2-1:0] exp_l2b_dout;
  logic [TOP_W*4-1:0] exp_l2b_l1_0_dout;
  logic [L0A_W-1:0] exp_l2b_l0a0_0_dout;
  logic [L0A_W-1:0] exp_l2b_l0a1_1_dout;
  logic [7:0] exp_l2b_l0b_1_dout;

  always_ff @(posedge clk) begin
    exp_l3_dout <= inst.tb_in ^ TOP_W'('1);

    exp_l2a_dout <= inst.l2[0].tb_in ^ (TOP_W * 2)'('1);
    exp_l2a_l1_0_dout <= inst.l2[0].l1[0].tb_in ^ (TOP_W * 4)'('1);
    exp_l2a_l0a0_0_dout <= inst.l2[0].l1[0].l0a[0].tb_in ^ L0A_W'('1);
    exp_l2a_l0a1_1_dout <= inst.l2[0].l1[1].l0a[1].tb_in ^ L0A_W'('1);
    exp_l2a_l0b_1_dout <= inst.l2[0].l1[1].l0b.tb_in ^ 8'hFF;

    exp_l2b_dout <= inst.l2[1].tb_in ^ (TOP_W * 2)'('1);
    exp_l2b_l1_0_dout <= inst.l2[1].l1[0].tb_in ^ (TOP_W * 4)'('1);
    exp_l2b_l0a0_0_dout <= inst.l2[1].l1[0].l0a[0].tb_in ^ L0A_W'('1);
    exp_l2b_l0a1_1_dout <= inst.l2[1].l1[1].l0a[1].tb_in ^ L0A_W'('1);
    exp_l2b_l0b_1_dout <= inst.l2[1].l1[1].l0b.tb_in ^ 8'hFF;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;

    if (cyc > 3) begin
      if (l3_dout !== exp_l3_dout) begin
        $display("FAIL cyc=%0d: l3_dout=%h expected %h", cyc, l3_dout, exp_l3_dout);
        $stop;
      end
      if (l2a_dout !== exp_l2a_dout) begin
        $display("FAIL cyc=%0d: l2a_dout=%h expected %h", cyc, l2a_dout, exp_l2a_dout);
        $stop;
      end
      if (l2a_l1_0_dout !== exp_l2a_l1_0_dout) begin
        $display("FAIL cyc=%0d: l2a_l1_0_dout=%h expected %h", cyc, l2a_l1_0_dout,
                 exp_l2a_l1_0_dout);
        $stop;
      end
      if (l2a_l0a0_0_dout !== exp_l2a_l0a0_0_dout) begin
        $display("FAIL cyc=%0d: l2a_l0a0_0_dout=%h expected %h", cyc, l2a_l0a0_0_dout,
                 exp_l2a_l0a0_0_dout);
        $stop;
      end
      if (l2a_l0a1_1_dout !== exp_l2a_l0a1_1_dout) begin
        $display("FAIL cyc=%0d: l2a_l0a1_1_dout=%h expected %h", cyc, l2a_l0a1_1_dout,
                 exp_l2a_l0a1_1_dout);
        $stop;
      end
      if (l2a_l0b_1_dout !== exp_l2a_l0b_1_dout) begin
        $display("FAIL cyc=%0d: l2a_l0b_1_dout=%h expected %h", cyc, l2a_l0b_1_dout,
                 exp_l2a_l0b_1_dout);
        $stop;
      end

      if (l2b_dout !== exp_l2b_dout) begin
        $display("FAIL cyc=%0d: l2b_dout=%h expected %h", cyc, l2b_dout, exp_l2b_dout);
        $stop;
      end
      if (l2b_l1_0_dout !== exp_l2b_l1_0_dout) begin
        $display("FAIL cyc=%0d: l2b_l1_0_dout=%h expected %h", cyc, l2b_l1_0_dout,
                 exp_l2b_l1_0_dout);
        $stop;
      end
      if (l2b_l0a0_0_dout !== exp_l2b_l0a0_0_dout) begin
        $display("FAIL cyc=%0d: l2b_l0a0_0_dout=%h expected %h", cyc, l2b_l0a0_0_dout,
                 exp_l2b_l0a0_0_dout);
        $stop;
      end
      if (l2b_l0a1_1_dout !== exp_l2b_l0a1_1_dout) begin
        $display("FAIL cyc=%0d: l2b_l0a1_1_dout=%h expected %h", cyc, l2b_l0a1_1_dout,
                 exp_l2b_l0a1_1_dout);
        $stop;
      end
      if (l2b_l0b_1_dout !== exp_l2b_l0b_1_dout) begin
        $display("FAIL cyc=%0d: l2b_l0b_1_dout=%h expected %h", cyc, l2b_l0b_1_dout,
                 exp_l2b_l0b_1_dout);
        $stop;
      end
    end

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
