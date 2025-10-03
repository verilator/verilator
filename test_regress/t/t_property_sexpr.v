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

  bit [3:0] val = 0;
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
  integer cyc = 1;

  always @(negedge clk) begin
    val <= 4'(cyc % 4);

    if (cyc >= 0 && cyc <= 4) begin
      ->e1;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e1", $time);
`endif
    end
    if (cyc >= 5 && cyc <= 10) begin
      ->e2;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e2", $time);
`endif
    end
    if (cyc >= 11 && cyc <= 15) begin
      ->e3;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e3", $time);
`endif
    end
    if (cyc >= 16 && cyc <= 20) begin
      ->e4;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e4", $time);
`endif
    end
    if (cyc >= 21 && cyc <= 25) begin
      ->e5;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e5", $time);
`endif
    end
    if (cyc >= 26 && cyc <= 30) begin
      ->e6;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e6", $time);
`endif
    end
    if (cyc >= 31 && cyc <= 35) begin
      ->e7;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e7", $time);
`endif
    end
    if (cyc >= 36 && cyc <= 40) begin
      ->e8;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e8", $time);
`endif
    end
    if (cyc >= 41 && cyc <= 45) begin
      ->e9;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e9", $time);
`endif
    end
    if (cyc >= 46 && cyc <= 50) begin
      ->e10;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e10", $time);
`endif
    end
    if (cyc >= 51 && cyc <= 55) begin
      ->e11;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e11", $time);
`endif
    end
    if (cyc >= 56 && cyc <= 60) begin
      ->e12;
`ifdef TEST_VERBOSE
      $display("[%0t] triggered e12", $time);
`endif
    end
`ifdef TEST_VERBOSE
    $display("cyc=%0d val=%0d", cyc, val);
`endif
    cyc <= cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  assert property (@(e1) ##1 1)
    $display("[%0t] single delay with const stmt, fileline:%0d", $time, `__LINE__);

  assert property (@(e2) ##1 val[0])
    $display("[%0t] single delay with var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with var else, fileline:%0d", $time, `__LINE__);

  assert property (@(e3) ##2 val[0])
    $display("[%0t] single multi-cycle delay with var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single multi-cycle delay with var else, fileline:%0d", $time, `__LINE__);

  assert property (@(e4) ##1 (val[0]))
    $display("[%0t] single delay with var brackets 1 stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with var brackets 1 else, fileline:%0d", $time, `__LINE__);

  assert property (@(e5) (##1 (val[0])))
    $display("[%0t] single delay with var brackets 2 stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with var brackets 2 else, fileline:%0d", $time, `__LINE__);

  assert property (@(e6) (##1 val[0] && val[1]))
    $display("[%0t] single delay with negated var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with negated var else, fileline:%0d", $time, `__LINE__);

  assert property (@(e7) not ##1 val[0])
    $display("[%0t] single delay with negated var stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with negated var else, fileline:%0d", $time, `__LINE__);

  assume property (@(e8) not (##1 val[0]))
    $display("[%0t] single delay with negated var brackets stmt, fileline:%0d", $time, `__LINE__);
  else
    $display("[%0t] single delay with negated var brackets else, fileline:%0d", $time, `__LINE__);

  assume property (@(e9) not (##1 val[0]))
  else
    $display("[%0t] single delay with negated var brackets else, fileline:%0d", $time, `__LINE__);

  assert property (@(e10) not (not ##1 val[0]))
    $display("[%0t] single delay with nested not stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] single delay with nested not else, fileline:%0d", $time, `__LINE__);

  restrict property (@(e11) ##1 val[0]);

  restrict property (@(e11) not ##1 val[0]);

  property prop;
    @(e12) not ##1 val[0]
  endproperty

  assert property (prop) $display("[%0t] property, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] property, fileline:%0d", $time, `__LINE__);

  assert property (@(posedge clk) not (not ##2 val[0] && val[1]))
    $display("[%0t] concurrent assert stmt, fileline:%0d", $time, `__LINE__);
  else $display("[%0t] concurrent assert else, fileline:%0d", $time, `__LINE__);
endmodule
