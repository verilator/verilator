// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define STRINGIFY(x) `"x`"
`define TRIGGER(e) ->e; $display("[%0t] triggered %s", $time, `STRINGIFY(e))

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;

  bit [1:0] val = 0;
  event e1;
  event e2;
  event e3;
  event e4;
  event e5;
  event e6;
  event e7;
  event e8;
  event e9;
  event e10;
  event e11;
  event e12;
  event e13;
  event e14;
  event e15;

  integer cyc = 1;

  always @(posedge clk) begin
    ++val;
    ++cyc;
`ifdef TEST_VERBOSE
    $display("[%0t] cyc=%0d val=%0d", $time, cyc, val);
`endif
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
  always @(negedge clk) begin
    if (cyc >= 0 && cyc <= 4) begin
      `TRIGGER(e1);
    end
    if (cyc >= 5 && cyc <= 10) begin
      `TRIGGER(e2);
    end
    if (cyc >= 11 && cyc <= 15) begin
      `TRIGGER(e3);
    end
    if (cyc >= 16 && cyc <= 20) begin
      `TRIGGER(e4);
    end
    if (cyc >= 21 && cyc <= 25) begin
      `TRIGGER(e5);
    end
    if (cyc >= 26 && cyc <= 30) begin
      `TRIGGER(e6);
    end
    if (cyc >= 31 && cyc <= 35) begin
      `TRIGGER(e7);
    end
    if (cyc >= 36 && cyc <= 40) begin
      `TRIGGER(e8);
    end
    if (cyc >= 41 && cyc <= 45) begin
      `TRIGGER(e9);
    end
    if (cyc >= 46 && cyc <= 50) begin
      `TRIGGER(e10);
    end
    if (cyc >= 51 && cyc <= 55) begin
      `TRIGGER(e11);
    end
    if (cyc >= 56 && cyc <= 60) begin
      `TRIGGER(e12);
    end
    if (cyc >= 61 && cyc <= 65) begin
      `TRIGGER(e13);
    end
    if (cyc >= 66 && cyc <= 70) begin
      `TRIGGER(e14);
    end
    if (cyc >= 71 && cyc <= 75) begin
      `TRIGGER(e15);
    end
  end


  assert property (@(e1) ##1 1);

  assert property (@(e1) ##1 1)
    $display("[%0t] single delay with const stmt, fileline:%0d", $time, `__LINE__);

  assert property (@(e2) ##1 val[0])
    $display("[%0t] single delay with var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with var else, fileline:%0d", $time, `__LINE__);

  assert property (@(e3) ##1 val[0]) begin
    $display("[%0t] stmt1, fileline:%0d", $time, `__LINE__);
    $display("[%0t] stmt2, fileline:%0d", $time, `__LINE__);
  end
  else begin
    $display("[%0t] else1, fileline:%0d", $time, `__LINE__);
    $display("[%0t] else2, fileline:%0d", $time, `__LINE__);
  end

  assert property (@(e4) ##2 val[0])
    $display("[%0t] single multi-cycle delay with var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single multi-cycle delay with var else, fileline:%0d", $time, `__LINE__);

  assert property (@(e5) ##1 (val[0]))
    $display("[%0t] single delay with var brackets 1 stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with var brackets 1 else, fileline:%0d", $time, `__LINE__);

  assert property (@(e6) (##1 (val[0])))
    $display("[%0t] single delay with var brackets 2 stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with var brackets 2 else, fileline:%0d", $time, `__LINE__);

  assert property (@(e7) (##1 val[0] && val[1]))
    $display("[%0t] single delay with and var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with and var else, fileline:%0d", $time, `__LINE__);

  assert property (@(e8) not not not ##1 val[0])
    $display("[%0t] single delay with negated var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with negated var else, fileline:%0d", $time, `__LINE__);

  assume property (@(e9) not (##1 val[0]))
    $display("[%0t] single delay with negated var brackets stmt, fileline:%0d", $time, `__LINE__);
  else
    $display("[%0t] single delay with negated var brackets else, fileline:%0d", $time, `__LINE__);

  assume property (@(e10) not (##1 val[0]))
  else
    $display("[%0t] single delay with negated var brackets else, fileline:%0d", $time, `__LINE__);

  assert property (@(e11) not (not ##1 val[0]))
    $display("[%0t] single delay with nested not stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with nested not else, fileline:%0d", $time, `__LINE__);

  assert property (@(e12) not (not ##2 val[0] && val[0]))
    $display("[%0t] stmt, fileline:%d", $time, `__LINE__);
  else
    $display("[%0t] else, fileline:%d", $time, `__LINE__);
`ifdef VERILATOR
  restrict property (@(e12) ##1 val[0]);

  restrict property (@(e12) not ##1 val[0]);
`endif
  property prop;
    @(e13) not ##1 val[0]
  endproperty

  assert property (prop) $display("[%0t] property, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] property, fileline:%0d", $time, `__LINE__);

  assert property (@(e14) val[0] ##2 val[1])
    $display("[%0t] stmt, fileline:%d", $time, `__LINE__);
  else
    $display("[%0t] else, fileline:%d", $time, `__LINE__);

  assert property (@(e15) val[0] ##1 val[1] ##1 val[0])
    $display("[%0t] stmt, fileline:%d", $time, `__LINE__);
  else
    $display("[%0t] else, fileline:%d", $time, `__LINE__);
endmodule
