// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;
  integer cyc = 1;
  bit val = 0;

  Test test (  /*AUTOINST*/
      // Inputs
      .clk(clk),
      .val(val),
      .cyc(cyc)
  );

  Ieee ieee();

  always @(posedge clk) begin
    if (cyc != 0) begin
      cyc <= cyc + 1;
      val = ~val;
`ifdef TEST_VERBOSE
      $display("cyc=%0d, val=%0d", cyc, val);
`endif
      if (cyc == 10) begin
        $write("*-* All Finished *-*\n");
        $finish;
      end
    end
  end
endmodule

module Test (
    input clk,
    input bit val,
    input integer cyc
);

  assert property (@(posedge clk) ##2 val)
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 1 |=> 0)
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 1 |=> not (val))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 val)
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 (val))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) (##1 (val)))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) (##1 (val)))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) not (##1 val))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 1 |=> 1)
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 val |=> not val)
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ##1 (val) |=> not (val))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) ((val) |=> not (val)))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) disable iff (cyc < 3) ##1 1 |=> cyc > 3)
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);

  assert property (@(posedge clk) (##1 val) |=> (##1 val))
  else $display("[%0t] assertion triggered, fileline:%d", $time, `__LINE__);
endmodule

// Test parsing only
module Ieee;
  // IEEE 1800-2023 16.6
  bit a;
  integer b;
  byte q[$];
  logic clk;

  property p1;
    $rose(a) |-> q[0];
  endproperty

  property p2;
    integer l_b;
    ($rose(a), l_b = b) |-> ##[3:10] q[l_b];
  endproperty

  bit [2:0] count = 0;
  realtime t;
  always @(posedge clk) begin
    if (count == 0) t = $realtime;
    count++;
  end
  property p3;
    @(posedge clk)
    count == 7 |-> $realtime - t < 50.5;
  endproperty

  property p4;
    realtime l_t;
    @(posedge clk)
    (count == 0, l_t = $realtime) ##1 (count == 7)[->1] |-> $realtime - l_t < 50.5;
  endproperty

  // IEEE 1800-2023 16.12.3
  assert property (@clk not a ##1 b);
endmodule
