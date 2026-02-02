// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Test nested interface ports with type parameters
//
// Tests all parameter patterns in a 5-deep hierarchy using types:
//   - Derived:     Type width doubles at each level (L3=bits(T)*2, etc.)
//   - Hard-coded:  L2B.T=logic[7:0] regardless of parent
//   - Passthrough: L0A_T flows unchanged from top to L0A
//   - Default:     L0B uses default T=logic[7:0]
//
// With TOP_T=logic[3:0], L0A_T=logic[15:0]:
//   L4(T=4b) -> L3(T=8b) -> L2A(T=16b) -> L1(T=32b) -> L0A(T=16b), L0B(T=8b)
//                        -> L2B(T=8b)  -> L1(T=16b) -> L0A(T=16b), L0B(T=8b)

interface l0_if #(parameter type T = logic [7:0]);
  T tb_in;
  T dut_out;
endinterface

interface l1_if #(parameter type T = logic, parameter type L0A_T = logic);
  T tb_in;
  T dut_out;
  l0_if #(.T(L0A_T)) l0a();  // passthrough
  l0_if              l0b();  // default
endinterface

interface l2_if #(parameter type T = logic, parameter type L0A_T = logic);
  T tb_in;
  T dut_out;
  l1_if #(.T(logic [$bits(T)*2-1:0]), .L0A_T(L0A_T)) l1();  // derived
endinterface

interface l3_if #(parameter type T = logic, parameter type L0A_T = logic);
  T tb_in;
  T dut_out;
  l2_if #(.T(logic [$bits(T)*2-1:0]), .L0A_T(L0A_T)) l2a();  // derived
  l2_if #(.T(logic [7:0]), .L0A_T(L0A_T)) l2b();  // hard-coded
endinterface

interface l4_if #(parameter type T = logic, parameter type L0A_T = logic);
  T tb_in;
  T dut_out;
  l3_if #(.T(logic [$bits(T)*2-1:0]), .L0A_T(L0A_T)) l3();  // derived
endinterface

// Handlers use type parameters with derived output types

module l0_handler #(parameter type T = logic [7:0])(
  input  logic clk,
  l0_if        l0,
  output T     dout
);
  always_ff @(posedge clk) l0.dut_out <= l0.tb_in ^ T'('1);
  assign dout = l0.dut_out;
endmodule

module l1_handler #(parameter type T = logic, parameter type L0A_T = logic)(
  input  logic       clk,
  l1_if              l1,
  output T           l1_dout,
  output L0A_T       l0a_dout,
  output logic [7:0] l0b_dout
);
  always_ff @(posedge clk) l1.dut_out <= l1.tb_in ^ T'('1);
  assign l1_dout = l1.dut_out;
  l0_handler #(.T(L0A_T))       m_l0a (.clk(clk), .l0(l1.l0a), .dout(l0a_dout));
  l0_handler #(.T(logic [7:0])) m_l0b (.clk(clk), .l0(l1.l0b), .dout(l0b_dout));
endmodule

module l2_handler #(parameter type T = logic, parameter type L0A_T = logic)(
  input  logic                   clk,
  l2_if                          l2,
  output T                       l2_dout,
  output logic [$bits(T)*2-1:0]  l1_dout,
  output L0A_T                   l0a_dout,
  output logic [7:0]             l0b_dout
);
  always_ff @(posedge clk) l2.dut_out <= l2.tb_in ^ T'('1);
  assign l2_dout = l2.dut_out;
  l1_handler #(.T(logic [$bits(T)*2-1:0]), .L0A_T(L0A_T)) m_l1 (
    .clk(clk), .l1(l2.l1),
    .l1_dout(l1_dout), .l0a_dout(l0a_dout), .l0b_dout(l0b_dout)
  );
endmodule

module l3_handler #(parameter type T = logic, parameter type L0A_T = logic)(
  input  logic                   clk,
  l3_if                          l3,
  output T                       l3_dout,
  output logic [$bits(T)*2-1:0]  l2a_dout,
  output logic [$bits(T)*4-1:0]  l1_2a_dout,
  output L0A_T                   l0a_2a_dout,
  output logic [7:0]             l0b_2a_dout,
  output logic [7:0]             l2b_dout,
  output logic [15:0]            l1_2b_dout,
  output L0A_T                   l0a_2b_dout,
  output logic [7:0]             l0b_2b_dout
);
  always_ff @(posedge clk) l3.dut_out <= l3.tb_in ^ T'('1);
  assign l3_dout = l3.dut_out;
  l2_handler #(.T(logic [$bits(T)*2-1:0]), .L0A_T(L0A_T)) m_l2a (
    .clk(clk), .l2(l3.l2a),
    .l2_dout(l2a_dout), .l1_dout(l1_2a_dout),
    .l0a_dout(l0a_2a_dout), .l0b_dout(l0b_2a_dout)
  );
  l2_handler #(.T(logic [7:0]), .L0A_T(L0A_T)) m_l2b (
    .clk(clk), .l2(l3.l2b),
    .l2_dout(l2b_dout), .l1_dout(l1_2b_dout),
    .l0a_dout(l0a_2b_dout), .l0b_dout(l0b_2b_dout)
  );
endmodule

module l4_handler #(parameter type T = logic, parameter type L0A_T = logic)(
  input  logic                   clk,
  l4_if                          l4,
  output T                       l4_dout,
  output logic [$bits(T)*2-1:0]  l3_dout,
  output logic [$bits(T)*4-1:0]  l2a_dout,
  output logic [$bits(T)*8-1:0]  l1_2a_dout,
  output L0A_T                   l0a_2a_dout,
  output logic [7:0]             l0b_2a_dout,
  output logic [7:0]             l2b_dout,
  output logic [15:0]            l1_2b_dout,
  output L0A_T                   l0a_2b_dout,
  output logic [7:0]             l0b_2b_dout
);
  always_ff @(posedge clk) l4.dut_out <= l4.tb_in ^ T'('1);
  assign l4_dout = l4.dut_out;
  l3_handler #(.T(logic [$bits(T)*2-1:0]), .L0A_T(L0A_T)) m_l3 (
    .clk(clk), .l3(l4.l3),
    .l3_dout(l3_dout),
    .l2a_dout(l2a_dout), .l1_2a_dout(l1_2a_dout),
    .l0a_2a_dout(l0a_2a_dout), .l0b_2a_dout(l0b_2a_dout),
    .l2b_dout(l2b_dout), .l1_2b_dout(l1_2b_dout),
    .l0a_2b_dout(l0a_2b_dout), .l0b_2b_dout(l0b_2b_dout)
  );
endmodule

module t;
  logic clk = 0;
  int   cyc = 0;

  localparam type TOP_T = logic [3:0];
  localparam type L0A_T = logic [15:0];

  l4_if #(.T(TOP_T), .L0A_T(L0A_T)) inst();

  logic [3:0]  l4_dout;
  logic [7:0]  l3_dout;
  logic [15:0] l2a_dout;
  logic [31:0] l1_2a_dout;
  logic [15:0] l0a_2a_dout;
  logic [7:0]  l0b_2a_dout;
  logic [7:0]  l2b_dout;
  logic [15:0] l1_2b_dout;
  logic [15:0] l0a_2b_dout;
  logic [7:0]  l0b_2b_dout;

  l4_handler #(.T(TOP_T), .L0A_T(L0A_T)) m_l4 (
    .clk(clk), .l4(inst),
    .l4_dout(l4_dout),
    .l3_dout(l3_dout),
    .l2a_dout(l2a_dout), .l1_2a_dout(l1_2a_dout),
    .l0a_2a_dout(l0a_2a_dout), .l0b_2a_dout(l0b_2a_dout),
    .l2b_dout(l2b_dout), .l1_2b_dout(l1_2b_dout),
    .l0a_2b_dout(l0a_2b_dout), .l0b_2b_dout(l0b_2b_dout)
  );

  always #5 clk = ~clk;

  always_ff @(posedge clk) begin
    inst.tb_in               <= cyc[3:0];
    inst.l3.tb_in            <= cyc[7:0] + 8'd1;
    inst.l3.l2a.tb_in        <= cyc[15:0] + 16'd2;
    inst.l3.l2a.l1.tb_in     <= cyc[31:0] + 32'd3;
    inst.l3.l2a.l1.l0a.tb_in <= cyc[15:0] + 16'd4;
    inst.l3.l2a.l1.l0b.tb_in <= cyc[7:0] + 8'd5;
    inst.l3.l2b.tb_in        <= cyc[7:0] + 8'd6;
    inst.l3.l2b.l1.tb_in     <= cyc[15:0] + 16'd7;
    inst.l3.l2b.l1.l0a.tb_in <= cyc[15:0] + 16'd8;
    inst.l3.l2b.l1.l0b.tb_in <= cyc[7:0] + 8'd9;
  end

  logic [3:0]  exp_l4;
  logic [7:0]  exp_l3;
  logic [15:0] exp_l2a;
  logic [31:0] exp_l1_2a;
  logic [15:0] exp_l0a_2a;
  logic [7:0]  exp_l0b_2a;
  logic [7:0]  exp_l2b;
  logic [15:0] exp_l1_2b;
  logic [15:0] exp_l0a_2b;
  logic [7:0]  exp_l0b_2b;

  always_ff @(posedge clk) begin
    exp_l4     <= inst.tb_in ^ 4'hF;
    exp_l3     <= inst.l3.tb_in ^ 8'hFF;
    exp_l2a    <= inst.l3.l2a.tb_in ^ 16'hFFFF;
    exp_l1_2a  <= inst.l3.l2a.l1.tb_in ^ 32'hFFFFFFFF;
    exp_l0a_2a <= inst.l3.l2a.l1.l0a.tb_in ^ 16'hFFFF;
    exp_l0b_2a <= inst.l3.l2a.l1.l0b.tb_in ^ 8'hFF;
    exp_l2b    <= inst.l3.l2b.tb_in ^ 8'hFF;
    exp_l1_2b  <= inst.l3.l2b.l1.tb_in ^ 16'hFFFF;
    exp_l0a_2b <= inst.l3.l2b.l1.l0a.tb_in ^ 16'hFFFF;
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
