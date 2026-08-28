// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Aisha Salimgereyeva
// SPDX-License-Identifier: CC0-1.0


module t (
    input wire clk,
    input wire clka,
    input wire clkb,
    input wire d,
    input wire [3:0] dv,
    output logic q1,
    output logic q2,
    output logic [3:0] q3a,
    output logic [3:0] q3b,
    output logic [3:0] q3c
);

  t1 u1 (
      .clk(clk),
      .d  (d),
      .q  (q1)
  );

  t2 u2 (
      .clka(clka),
      .clkb(clkb),
      .d   (d),
      .q   (q2)
  );

  t3 u3 (
      .clk(clk),
      .d  (dv),
      .q1 (q3a),
      .q2 (q3b),
      .q3 (q3c)
  );

endmodule


// Same clock: two plain always blocks drive the whole of 'q', reported by
// MULTIDRIVENPROC.
module t1 (
    input wire clk,
    input wire d,
    output logic q
);

  always @(posedge clk) q <= d;
  always @(posedge clk) q <= ~d;

endmodule

// Different clocks: reported by MULTIDRIVEN (on by default). MULTIDRIVENPROC is
// suppressed here so the conflict is reported only once.
module t2 (
    input wire clka,
    input wire clkb,
    input wire d,
    output logic q
);

  always @(posedge clka) q <= d;
  always @(posedge clkb) q <= ~d;

endmodule

// A static loop induction variable should not warn.
module t3 (
    input wire clk,
    input wire [3:0] d,
    output logic [3:0] q1,
    output logic [3:0] q2,
    output logic [3:0] q3
);

  integer i;

  always @(posedge clk) begin
    for (i = 0; i < 4; i = i + 1) q1[i] <= d[i];
  end

  always @(posedge clk) begin
    for (i = 0; i < 4; i = i + 1) q2[i] <= ~d[i];
  end

  always @* begin
    for (i = 0; i < 4; i = i + 1) q3[i] = d[i] ^ q1[i];
  end

endmodule
