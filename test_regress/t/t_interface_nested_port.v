// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Test passing sub-interface of INTERFACE PORT to child module
// Tests 1-deep through 5-deep interface port passthrough
// Each handler instantiates the (N-1)_handler with its nested interface
//
// Mix of patterns to test both direct drive and driver/reader submodules:
// - L4, L2: direct drive (simple pattern)
// - L3, L1, leaf: driver/reader submodules (tests passing interface port to children)

// Interface hierarchy: l4 -> l3 -> l2 -> l1 -> leaf
// Each interface has tb_in (testbench driven) and dut_out (DUT driven)

interface leaf_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
endinterface

interface l1_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
  leaf_if     leaf();
endinterface

interface l2_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
  l1_if       l1();
endinterface

interface l3_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
  l2_if       l2();
endinterface

interface l4_if;
  logic [7:0] tb_in;
  logic [7:0] dut_out;
  l3_if       l3();
endinterface

// ============================================================================
// Driver/reader submodules - test passing interface port to children
// Used by L3, L1, and leaf handlers
// ============================================================================

module leaf_driver (input logic clk, leaf_if leaf);
  always_ff @(posedge clk) leaf.dut_out <= leaf.tb_in ^ 8'hFF;
endmodule

module leaf_reader (leaf_if leaf, output logic [7:0] dout);
  assign dout = leaf.dut_out;
endmodule

module l1_driver (input logic clk, l1_if l1);
  always_ff @(posedge clk) l1.dut_out <= l1.tb_in ^ 8'h11;
endmodule

module l1_reader (l1_if l1, output logic [7:0] dout);
  assign dout = l1.dut_out;
endmodule

module l3_driver (input logic clk, l3_if l3);
  always_ff @(posedge clk) l3.dut_out <= l3.tb_in ^ 8'h33;
endmodule

module l3_reader (l3_if l3, output logic [7:0] dout);
  assign dout = l3.dut_out;
endmodule

// ============================================================================
// Leaf handler - uses driver/reader submodules
// ============================================================================

module leaf_handler (
  input  logic       clk,
  leaf_if            leaf,
  output logic [7:0] dout
);
  leaf_driver m_drv (.clk(clk), .leaf(leaf));
  leaf_reader m_rdr (.leaf(leaf), .dout(dout));
endmodule

// ============================================================================
// L1 handler - uses driver/reader submodules
// ============================================================================

module l1_handler (
  input  logic       clk,
  l1_if              l1,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  l1_driver m_drv (.clk(clk), .l1(l1));
  l1_reader m_rdr (.l1(l1), .dout(l1_dout));
  leaf_handler m_leaf (.clk(clk), .leaf(l1.leaf), .dout(leaf_dout));
endmodule

// ============================================================================
// L2 handler - uses direct drive
// ============================================================================

module l2_handler (
  input  logic       clk,
  l2_if              l2,
  output logic [7:0] l2_dout,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  always_ff @(posedge clk) l2.dut_out <= l2.tb_in ^ 8'h22;
  assign l2_dout = l2.dut_out;
  l1_handler m_l1 (.clk(clk), .l1(l2.l1), .l1_dout(l1_dout), .leaf_dout(leaf_dout));
endmodule

// ============================================================================
// L3 handler - uses driver/reader submodules
// ============================================================================

module l3_handler (
  input  logic       clk,
  l3_if              l3,
  output logic [7:0] l3_dout,
  output logic [7:0] l2_dout,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  l3_driver m_drv (.clk(clk), .l3(l3));
  l3_reader m_rdr (.l3(l3), .dout(l3_dout));
  l2_handler m_l2 (.clk(clk), .l2(l3.l2), .l2_dout(l2_dout), .l1_dout(l1_dout), .leaf_dout(leaf_dout));
endmodule

// ============================================================================
// L4 handler - uses direct drive
// ============================================================================

module l4_handler (
  input  logic       clk,
  l4_if              l4,
  output logic [7:0] l4_dout,
  output logic [7:0] l3_dout,
  output logic [7:0] l2_dout,
  output logic [7:0] l1_dout,
  output logic [7:0] leaf_dout
);
  always_ff @(posedge clk) l4.dut_out <= l4.tb_in ^ 8'h44;
  assign l4_dout = l4.dut_out;
  l3_handler m_l3 (.clk(clk), .l3(l4.l3), .l3_dout(l3_dout), .l2_dout(l2_dout), .l1_dout(l1_dout), .leaf_dout(leaf_dout));
endmodule

// ============================================================================
// Testbench
// ============================================================================

module t;
  logic clk = 0;
  int   cyc = 0;

  // Local interface instance (5 levels deep)
  l4_if inst();

  // DUT outputs
  logic [7:0] l4_dout, l3_dout, l2_dout, l1_dout, leaf_dout;

  // Instantiate top-level handler
  l4_handler m_l4 (
    .clk(clk),
    .l4(inst),
    .l4_dout(l4_dout),
    .l3_dout(l3_dout),
    .l2_dout(l2_dout),
    .l1_dout(l1_dout),
    .leaf_dout(leaf_dout)
  );

  always #5 clk = ~clk;

  // Testbench drives tb_in at each level
  always_ff @(posedge clk) begin
    inst.tb_in               <= cyc[7:0];
    inst.l3.tb_in            <= cyc[7:0] + 8'd10;
    inst.l3.l2.tb_in         <= cyc[7:0] + 8'd20;
    inst.l3.l2.l1.tb_in      <= cyc[7:0] + 8'd30;
    inst.l3.l2.l1.leaf.tb_in <= cyc[7:0] + 8'd40;
  end

  // Expected values (2-cycle delay: TB writes, then handler computes)
  logic [7:0] exp_l4, exp_l3, exp_l2, exp_l1, exp_leaf;

  always_ff @(posedge clk) begin
    exp_l4   <= inst.tb_in ^ 8'h44;
    exp_l3   <= inst.l3.tb_in ^ 8'h33;
    exp_l2   <= inst.l3.l2.tb_in ^ 8'h22;
    exp_l1   <= inst.l3.l2.l1.tb_in ^ 8'h11;
    exp_leaf <= inst.l3.l2.l1.leaf.tb_in ^ 8'hFF;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;

    if (cyc > 3) begin
      // Check L4 (1-deep from testbench) - direct drive
      if (inst.dut_out !== exp_l4) begin
        $display("FAIL cyc=%0d: l4.dut_out=%h expected %h", cyc, inst.dut_out, exp_l4);
        $stop;
      end
      if (l4_dout !== exp_l4) begin
        $display("FAIL cyc=%0d: l4_dout=%h expected %h", cyc, l4_dout, exp_l4);
        $stop;
      end

      // Check L3 (2-deep) - driver/reader submodules
      if (inst.l3.dut_out !== exp_l3) begin
        $display("FAIL cyc=%0d: l3.dut_out=%h expected %h", cyc, inst.l3.dut_out, exp_l3);
        $stop;
      end
      if (l3_dout !== exp_l3) begin
        $display("FAIL cyc=%0d: l3_dout=%h expected %h", cyc, l3_dout, exp_l3);
        $stop;
      end

      // Check L2 (3-deep) - direct drive
      if (inst.l3.l2.dut_out !== exp_l2) begin
        $display("FAIL cyc=%0d: l2.dut_out=%h expected %h", cyc, inst.l3.l2.dut_out, exp_l2);
        $stop;
      end
      if (l2_dout !== exp_l2) begin
        $display("FAIL cyc=%0d: l2_dout=%h expected %h", cyc, l2_dout, exp_l2);
        $stop;
      end

      // Check L1 (4-deep) - driver/reader submodules
      if (inst.l3.l2.l1.dut_out !== exp_l1) begin
        $display("FAIL cyc=%0d: l1.dut_out=%h expected %h", cyc, inst.l3.l2.l1.dut_out, exp_l1);
        $stop;
      end
      if (l1_dout !== exp_l1) begin
        $display("FAIL cyc=%0d: l1_dout=%h expected %h", cyc, l1_dout, exp_l1);
        $stop;
      end

      // Check leaf (5-deep) - driver/reader submodules
      if (inst.l3.l2.l1.leaf.dut_out !== exp_leaf) begin
        $display("FAIL cyc=%0d: leaf.dut_out=%h expected %h", cyc, inst.l3.l2.l1.leaf.dut_out, exp_leaf);
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
