// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

package P;
  typedef struct {
    logic [7:0] va[int];
    logic [7:0] vw[*];
  } C;
  typedef struct {
    C a;
    int b;
  } B;
  typedef struct {B a;} A;
endpackage
module t (
    input P::A a,
    output logic b,
    output logic c
);
  assign b = (a.a.a.va[0] == 8'h0);
  assign c = (a.a.a.vw[0] == 8'h0);

  initial begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
