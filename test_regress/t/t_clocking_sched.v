// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2022 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module t (/*AUTOARG*/
  // Inputs
  clk
  );
  input clk;
  int cyc = 0;

  always @(negedge clk) begin  // negedge so there is nothing after $finish
     cyc <= cyc + 1;
     if (cyc == 2) begin
        $write("*-* All Finished *-*\n");
        $finish;
     end
  end

  logic genclk = 0, a = 0, b = 1, c = 0, x = 0, y, z = 0;
  always @(edge clk) genclk = clk;
  always @(posedge genclk) $display("%0t | posedge", $time);

  // Clocking block
  clocking cb @(posedge genclk);
    input #0 a, y;
    input #1step b;
    output #0 x;
`ifdef VERILATOR_TIMING
    output #2 z;
`endif
  endclocking

  // Print after Observed
  always @(posedge genclk) a = ~a;
  always @cb $display("%0t | cb.a=%b", $time, cb.a);
  always @cb $display("%0t | cb.b=%b", $time, cb.b);
  always @cb.y $display("%0t | cb.y=%b", $time, cb.y);

  // Retrigger everything after Observed
  always @cb.a b = x;
  always @b begin
    $display("%0t | b=%b", $time, b);
    if (b == 0) genclk = ~genclk;
  end

  // Do an NBA
  always @(posedge genclk) c <= ~c;
  always @c begin
    $display("%0t | c<=%b", $time, c);
  end

  // Print after Re-NBA
  always @(posedge genclk) cb.x <= ~x;
  always @x $display("%0t | x<=%b", $time, x);

  // Retrigger everything after Re-NBA
  always @x y = x;
  always @y begin
    $display("%0t | y=%b", $time, y);
    if (y == 1) genclk = ~genclk;
  end

`ifdef VERILATOR_TIMING
  // Print after delay and Re-NBA
  always @(posedge genclk) cb.z <= ~z;
  always @z $display("%0t | z<=%b", $time, z);
`endif

  // Print in Postponed
  always @(posedge genclk) $strobe("%0t | %b %b %b %b %b %b", $time, a, b, c, x, y, z);
endmodule;
