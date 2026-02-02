// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Test nested interface port with parameterized interfaces
// l2_if is parameterized; l3_if instantiates two versions with different widths

interface leaf_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
endinterface

interface l1_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
  leaf_if leaf();
endinterface

interface l2_if #(
  parameter int WIDTH = 8
);
  logic [WIDTH-1:0] tb_in;
  logic [WIDTH-1:0] dut_out;
  l1_if l1();
endinterface

interface l3_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
  l2_if #(8)  l2_a();
  l2_if #(16) l2_b();
endinterface

// ============================================================================
// Handlers
// ============================================================================

module leaf_handler (
  input  logic       clk,
  leaf_if            leaf,
  output logic [7:0] dout
);
  always_ff @(posedge clk) leaf.dut_out <= leaf.tb_in ^ 8'hFF;
  assign dout = leaf.dut_out;
endmodule

module l1_handler (
  input  logic       clk,
  l1_if              l1,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  always_ff @(posedge clk) l1.dut_out <= l1.tb_in ^ 8'h11;
  assign l1_dout = l1.dut_out;
  leaf_handler m_leaf (.clk(clk), .leaf(l1.leaf), .dout(leaf_dout));
endmodule

module l2_handler (
  input  logic       clk,
  l2_if              l2,
  output logic [7:0] l2_dout,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  always_ff @(posedge clk) l2.dut_out <= l2.tb_in ^ 8'h22;
  assign l2_dout = l2.dut_out[7:0];
  l1_handler m_l1 (.clk(clk), .l1(l2.l1), .l1_dout(l1_dout), .leaf_dout(leaf_dout));
endmodule

module l3_handler (
  input  logic       clk,
  l3_if              l3,
  output logic [7:0] l3_dout,
  output logic [7:0] l2_dout,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  always_ff @(posedge clk) l3.dut_out <= l3.tb_in ^ 8'h33;
  assign l3_dout = l3.dut_out;
  // Use l2_a (WIDTH=8) path
  l2_handler m_l2 (.clk(clk), .l2(l3.l2_a), .l2_dout(l2_dout), .l1_dout(l1_dout), .leaf_dout(leaf_dout));
endmodule

// ============================================================================
// Testbench
// ============================================================================

module t;
  logic clk = 0;
  int   cyc = 0;

  l3_if inst();

  logic [7:0] l3_dout, l2_dout, l1_dout, leaf_dout;

  l3_handler m_l3 (
    .clk(clk),
    .l3(inst),
    .l3_dout(l3_dout),
    .l2_dout(l2_dout),
    .l1_dout(l1_dout),
    .leaf_dout(leaf_dout)
  );

  always #5 clk = ~clk;

  always_ff @(posedge clk) begin
    inst.tb_in              <= cyc[7:0];
    inst.l2_a.tb_in         <= cyc[7:0] + 8'd10;
    inst.l2_a.l1.tb_in      <= cyc[7:0] + 8'd20;
    inst.l2_a.l1.leaf.tb_in <= cyc[7:0] + 8'd30;
  end

  logic [7:0] exp_l3, exp_l2, exp_l1, exp_leaf;

  always_ff @(posedge clk) begin
    exp_l3   <= inst.tb_in ^ 8'h33;
    exp_l2   <= inst.l2_a.tb_in[7:0] ^ 8'h22;
    exp_l1   <= inst.l2_a.l1.tb_in ^ 8'h11;
    exp_leaf <= inst.l2_a.l1.leaf.tb_in ^ 8'hFF;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;

    if (cyc > 3) begin
      if (l3_dout !== exp_l3) begin
        $display("FAIL cyc=%0d: l3_dout=%h expected %h", cyc, l3_dout, exp_l3);
        $stop;
      end
      if (l2_dout !== exp_l2) begin
        $display("FAIL cyc=%0d: l2_dout=%h expected %h", cyc, l2_dout, exp_l2);
        $stop;
      end
      if (l1_dout !== exp_l1) begin
        $display("FAIL cyc=%0d: l1_dout=%h expected %h", cyc, l1_dout, exp_l1);
        $stop;
      end
      if (leaf_dout !== exp_leaf) begin
        $display("FAIL cyc=%0d: leaf_dout=%h expected %h", cyc, leaf_dout, exp_leaf);
        $stop;
      end
    end

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
