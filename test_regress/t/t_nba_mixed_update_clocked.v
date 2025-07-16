// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define check(got ,exp) do if ((got) !== (exp)) begin $write("%%Error: %s:%0d: cyc=%0d got='h%x exp='h%x\n", `__FILE__,`__LINE__, cyc, (got), (exp)); `stop; end while(0)

module t (/*AUTOARG*/
   // Inputs
   clk
   );
  input clk;

  reg [31:0] cyc = 0;

  // 'x' has both blocking and non-blocking update, with the blocking
  // update in **clocked** logic
  reg [1:0] x = 2'b00;
  // '{y1, y0}' should have exactly the same value as 'x', at all times
  reg y0 = 1'b0;
  reg y1 = 1'b0;
  // 'z[0]' should equal '{8{x[0]}', 'z[1]' should equal '{8{x[1]}}'
  reg [1:0][7:0] z;
  // 'pair.a' should equal 'x[0]', 'pair.b' should equal 'x[1]'
  struct {
    logic a;
    logic b;
  } pair = '{a: 1'b0, b: 1'b0};

  always @(posedge clk) begin
     $display("cyc = %d (%08x) x[1] = %0d, x[0] = %0d, y1 = %0d, y0 = %0d z[1] = %02x z[1] = %02x pair.a = %0d pair.b = %0d",
              cyc, cyc, x[1], x[0], y1, y0, z[1], z[0], pair.a, pair.b);
     `check(x[0], cyc[0]);
     `check(x[1], cyc[0]);
     `check(y0, cyc[0]);
     `check(y1, cyc[0]);
     `check(z[0], {8{cyc[0]}});
     `check(z[1], {8{cyc[0]}});
     `check(pair.a, cyc[0]);
     `check(pair.b, cyc[0]);
     x[1] <= ~x[1];
     y1 <= ~y1;
     for (int i = 0; i < 8; ++i) z[1][i] <= ~z[1][i];
     pair.b <= ~pair.b;
     cyc = cyc + 1;
     x[0] = cyc[0];
     y0 = cyc[0];
     for (int i = 0; i < 8; ++i) z[0][i] = cyc[0];
     pair.a = cyc[0];
     if (cyc == 99) begin
       $display(x);
       $write("*-* All Finished *-*\n");
       $finish;
     end
  end

endmodule
