// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Leela Pakanati
// SPDX-License-Identifier: CC0-1.0

// Issue #5066 - Test nested interface as port connection

interface A;
  typedef struct packed {
    logic [7:0] value;
    logic       valid;
  } data_t;

  logic x;
  data_t data;
endinterface

interface B;
  A a();
endinterface

interface C;
  B b();
endinterface

// Module taking interface A directly
module M1(A a, input logic clk);
  always @(posedge clk) begin
    a.x <= 1'b1;
    a.data.value <= a.data.value + 8'd1;
    a.data.valid <= 1'b1;
  end
endmodule

// Module taking interface B (2-level nesting at port)
module M2(B b, input logic clk);
  always @(posedge clk) begin
    b.a.x <= 1'b1;
    b.a.data.value <= b.a.data.value + 8'd2;
    b.a.data.valid <= 1'b1;
  end
endmodule

module t;
  logic clk = 0;
  int   cyc = 0;

  // 2-level nesting
  B b1();
  M1 m1(b1.a, clk);

  // 3-level nesting
  C c();
  M2 m2(c.b, clk);

  always #5 clk = ~clk;

  always @(posedge clk) begin
    cyc <= cyc + 1;

    if (cyc == 5) begin
      // Check 2-level nested interface (b1.a)
      if (b1.a.x !== 1'b1) $stop;
      if (b1.a.data.valid !== 1'b1) $stop;
      if (b1.a.data.value < 8'd5) $stop;

      // Check 3-level nested interface (c.b.a)
      if (c.b.a.x !== 1'b1) $stop;
      if (c.b.a.data.valid !== 1'b1) $stop;
      if (c.b.a.data.value < 8'd10) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
