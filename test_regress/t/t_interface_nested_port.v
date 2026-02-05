// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Combined test for nested interface ports with parameters
//
// Tests all parameter patterns in a 5-deep hierarchy:
//   - Derived:     W doubles at each level (L3=L4*2, L2A=L3*2, L1=L2*2)
//   - Hard-coded:  L2B.W=8 regardless of parent
//   - Passthrough: L0A_W flows unchanged from top to L0A
//   - Default:     L0B uses default W=8
//
// With TOP_W=4, L0A_W=16:
//   L4(W=4) -> L3(W=8) -> L2A(W=16) -> L1(W=32) -> L0A(W=16), L0B(W=8)
//                      -> L2B(W=8)  -> L1(W=16) -> L0A(W=16), L0B(W=8)

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
  l0_if #(L0A_W) l0a ();  // passthrough
  l0_if l0b ();  // default
endinterface

interface l2_if #(
    parameter int W = 8,
    parameter int L0A_W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
  l1_if #(W * 2, L0A_W) l1 ();  // derived
endinterface

interface l3_if #(
    parameter int W = 8,
    parameter int L0A_W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
  l2_if #(W * 2, L0A_W) l2a ();  // derived
  l2_if #(8, L0A_W) l2b ();  // hard-coded
endinterface

interface l4_if #(
    parameter int W = 8,
    parameter int L0A_W = 8
);
  logic [W-1:0] tb_in;
  logic [W-1:0] dut_out;
  l3_if #(W * 2, L0A_W) l3 ();  // derived
endinterface

// Handlers use unparameterized interface ports with parameterized output widths

module l0_handler #(
    parameter int W = 8
) (
    input logic clk,
    l0_if l0,
    output logic [W-1:0] dout
);
  always_ff @(posedge clk) l0.dut_out <= l0.tb_in ^ W'('1);
  assign dout = l0.dut_out;
endmodule

module l1_reader #(
    parameter int W = 8
) (
    l1_if l1,
    output logic [W-1:0] dout
);
  assign dout = l1.dut_out;
endmodule

module l1_driver #(
    parameter int W = 8
) (
    input logic clk,
    l1_if l1
);
  always_ff @(posedge clk) l1.dut_out <= l1.tb_in ^ W'('1);
endmodule

module l1_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l1_if l1,
    output logic [W-1:0] l1_dout,
    output logic [L0A_W-1:0] l0a_dout,
    output logic [7:0] l0b_dout
);
  // Use reader/driver submodules instead of direct access
  l1_reader #(W) m_rdr (
      .l1(l1),
      .dout(l1_dout)
  );
  l1_driver #(W) m_drv (
      .clk(clk),
      .l1(l1)
  );

  // Still instantiate l0_handlers for nested ports
  l0_handler #(L0A_W) m_l0a (
      .clk(clk),
      .l0(l1.l0a),
      .dout(l0a_dout)
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
    l2_if l2,
    output logic [W-1:0] l2_dout,
    output logic [W*2-1:0] l1_dout,
    output logic [L0A_W-1:0] l0a_dout,
    output logic [7:0] l0b_dout
);
  always_ff @(posedge clk) l2.dut_out <= l2.tb_in ^ W'('1);
  assign l2_dout = l2.dut_out;
  l1_handler #(W * 2, L0A_W) m_l1 (
      .clk(clk),
      .l1(l2.l1),
      .l1_dout(l1_dout),
      .l0a_dout(l0a_dout),
      .l0b_dout(l0b_dout)
  );
endmodule

module l3_reader #(
    parameter int W = 8
) (
    l3_if l3,
    output logic [W-1:0] dout
);
  assign dout = l3.dut_out;
endmodule

module l3_driver #(
    parameter int W = 8
) (
    input logic clk,
    l3_if l3
);
  always_ff @(posedge clk) l3.dut_out <= l3.tb_in ^ W'('1);
endmodule

module l3_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l3_if l3,
    output logic [W-1:0] l3_dout,
    output logic [W*2-1:0] l2a_dout,
    output logic [W*4-1:0] l1_2a_dout,
    output logic [L0A_W-1:0] l0a_2a_dout,
    output logic [7:0] l0b_2a_dout,
    output logic [7:0] l2b_dout,
    output logic [15:0] l1_2b_dout,
    output logic [L0A_W-1:0] l0a_2b_dout,
    output logic [7:0] l0b_2b_dout
);
  // Use reader/driver submodules instead of direct access
  l3_reader #(W) m_rdr (
      .l3(l3),
      .dout(l3_dout)
  );
  l3_driver #(W) m_drv (
      .clk(clk),
      .l3(l3)
  );

  // Still instantiate l2_handlers for nested ports
  l2_handler #(W * 2, L0A_W) m_l2a (
      .clk(clk),
      .l2(l3.l2a),
      .l2_dout(l2a_dout),
      .l1_dout(l1_2a_dout),
      .l0a_dout(l0a_2a_dout),
      .l0b_dout(l0b_2a_dout)
  );
  l2_handler #(8, L0A_W) m_l2b (
      .clk(clk),
      .l2(l3.l2b),
      .l2_dout(l2b_dout),
      .l1_dout(l1_2b_dout),
      .l0a_dout(l0a_2b_dout),
      .l0b_dout(l0b_2b_dout)
  );
endmodule

module l4_handler #(
    parameter int W = 8,
    parameter int L0A_W = 8
) (
    input logic clk,
    l4_if l4,
    output logic [W-1:0] l4_dout,
    output logic [W*2-1:0] l3_dout,
    output logic [W*4-1:0] l2a_dout,
    output logic [W*8-1:0] l1_2a_dout,
    output logic [L0A_W-1:0] l0a_2a_dout,
    output logic [7:0] l0b_2a_dout,
    output logic [7:0] l2b_dout,
    output logic [15:0] l1_2b_dout,
    output logic [L0A_W-1:0] l0a_2b_dout,
    output logic [7:0] l0b_2b_dout
);
  always_ff @(posedge clk) l4.dut_out <= l4.tb_in ^ W'('1);
  assign l4_dout = l4.dut_out;
  l3_handler #(W * 2, L0A_W) m_l3 (
      .clk(clk),
      .l3(l4.l3),
      .l3_dout(l3_dout),
      .l2a_dout(l2a_dout),
      .l1_2a_dout(l1_2a_dout),
      .l0a_2a_dout(l0a_2a_dout),
      .l0b_2a_dout(l0b_2a_dout),
      .l2b_dout(l2b_dout),
      .l1_2b_dout(l1_2b_dout),
      .l0a_2b_dout(l0a_2b_dout),
      .l0b_2b_dout(l0b_2b_dout)
  );
endmodule

module t;
  logic clk = 0;
  int cyc = 0;

  localparam int TOP_W = 4;
  localparam int L0A_W = 16;

  l4_if #(TOP_W, L0A_W) inst ();

  logic [TOP_W-1:0] l4_dout;
  logic [TOP_W*2-1:0] l3_dout;
  logic [TOP_W*4-1:0] l2a_dout;
  logic [TOP_W*8-1:0] l1_2a_dout;
  logic [L0A_W-1:0] l0a_2a_dout;
  logic [7:0] l0b_2a_dout;
  logic [7:0] l2b_dout;
  logic [15:0] l1_2b_dout;
  logic [L0A_W-1:0] l0a_2b_dout;
  logic [7:0] l0b_2b_dout;

  l4_handler #(TOP_W, L0A_W) m_l4 (
      .clk(clk),
      .l4(inst),
      .l4_dout(l4_dout),
      .l3_dout(l3_dout),
      .l2a_dout(l2a_dout),
      .l1_2a_dout(l1_2a_dout),
      .l0a_2a_dout(l0a_2a_dout),
      .l0b_2a_dout(l0b_2a_dout),
      .l2b_dout(l2b_dout),
      .l1_2b_dout(l1_2b_dout),
      .l0a_2b_dout(l0a_2b_dout),
      .l0b_2b_dout(l0b_2b_dout)
  );

  always #5 clk = ~clk;

  always_ff @(posedge clk) begin
    inst.tb_in <= cyc[TOP_W-1:0];
    inst.l3.tb_in <= cyc[TOP_W*2-1:0] + (TOP_W * 2)'(1);
    inst.l3.l2a.tb_in <= cyc[TOP_W*4-1:0] + (TOP_W * 4)'(2);
    inst.l3.l2a.l1.tb_in <= cyc[TOP_W*8-1:0] + (TOP_W * 8)'(3);
    inst.l3.l2a.l1.l0a.tb_in <= cyc[L0A_W-1:0] + L0A_W'(4);
    inst.l3.l2a.l1.l0b.tb_in <= cyc[7:0] + 8'd5;
    inst.l3.l2b.tb_in <= cyc[7:0] + 8'd6;
    inst.l3.l2b.l1.tb_in <= cyc[15:0] + 16'd7;
    inst.l3.l2b.l1.l0a.tb_in <= cyc[L0A_W-1:0] + L0A_W'(8);
    inst.l3.l2b.l1.l0b.tb_in <= cyc[7:0] + 8'd9;
  end

  logic [TOP_W-1:0] exp_l4;
  logic [TOP_W*2-1:0] exp_l3;
  logic [TOP_W*4-1:0] exp_l2a;
  logic [TOP_W*8-1:0] exp_l1_2a;
  logic [L0A_W-1:0] exp_l0a_2a;
  logic [7:0] exp_l0b_2a;
  logic [7:0] exp_l2b;
  logic [15:0] exp_l1_2b;
  logic [L0A_W-1:0] exp_l0a_2b;
  logic [7:0] exp_l0b_2b;

  always_ff @(posedge clk) begin
    exp_l4 <= inst.tb_in ^ TOP_W'('1);
    exp_l3 <= inst.l3.tb_in ^ (TOP_W * 2)'('1);
    exp_l2a <= inst.l3.l2a.tb_in ^ (TOP_W * 4)'('1);
    exp_l1_2a <= inst.l3.l2a.l1.tb_in ^ (TOP_W * 8)'('1);
    exp_l0a_2a <= inst.l3.l2a.l1.l0a.tb_in ^ L0A_W'('1);
    exp_l0b_2a <= inst.l3.l2a.l1.l0b.tb_in ^ 8'hFF;
    exp_l2b <= inst.l3.l2b.tb_in ^ 8'hFF;
    exp_l1_2b <= inst.l3.l2b.l1.tb_in ^ 16'hFFFF;
    exp_l0a_2b <= inst.l3.l2b.l1.l0a.tb_in ^ L0A_W'('1);
    exp_l0b_2b <= inst.l3.l2b.l1.l0b.tb_in ^ 8'hFF;
  end

  always @(posedge clk) begin
    cyc <= cyc + 1;

    if (cyc > 3) begin
      if (l4_dout !== exp_l4) begin
        $display("FAIL cyc=%0d: l4_dout=%h expected %h", cyc, l4_dout, exp_l4);
        $stop;
      end
      if (l3_dout !== exp_l3) begin
        $display("FAIL cyc=%0d: l3_dout=%h expected %h", cyc, l3_dout, exp_l3);
        $stop;
      end
      if (l2a_dout !== exp_l2a) begin
        $display("FAIL cyc=%0d: l2a_dout=%h expected %h", cyc, l2a_dout, exp_l2a);
        $stop;
      end
      if (l1_2a_dout !== exp_l1_2a) begin
        $display("FAIL cyc=%0d: l1_2a_dout=%h expected %h", cyc, l1_2a_dout, exp_l1_2a);
        $stop;
      end
      if (l0a_2a_dout !== exp_l0a_2a) begin
        $display("FAIL cyc=%0d: l0a_2a_dout=%h expected %h", cyc, l0a_2a_dout, exp_l0a_2a);
        $stop;
      end
      if (l0b_2a_dout !== exp_l0b_2a) begin
        $display("FAIL cyc=%0d: l0b_2a_dout=%h expected %h", cyc, l0b_2a_dout, exp_l0b_2a);
        $stop;
      end
      if (l2b_dout !== exp_l2b) begin
        $display("FAIL cyc=%0d: l2b_dout=%h expected %h", cyc, l2b_dout, exp_l2b);
        $stop;
      end
      if (l1_2b_dout !== exp_l1_2b) begin
        $display("FAIL cyc=%0d: l1_2b_dout=%h expected %h", cyc, l1_2b_dout, exp_l1_2b);
        $stop;
      end
      if (l0a_2b_dout !== exp_l0a_2b) begin
        $display("FAIL cyc=%0d: l0a_2b_dout=%h expected %h", cyc, l0a_2b_dout, exp_l0a_2b);
        $stop;
      end
      if (l0b_2b_dout !== exp_l0b_2b) begin
        $display("FAIL cyc=%0d: l0b_2b_dout=%h expected %h", cyc, l0b_2b_dout, exp_l0b_2b);
        $stop;
      end
    end

    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
