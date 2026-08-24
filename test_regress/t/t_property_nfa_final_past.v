// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// $past in 'final' for on-tick and between-tick simulation ends

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit clk = 0;
  bit data = 0;
  bit offedge = 0;
  bit exp_past = 0;
  int cyc = 0;

  always #1 clk = ~clk;

  default clocking cb @(posedge clk);
  endclocking

  function automatic bit fpast();
    return $past(data);
  endfunction

  function automatic bit fpast_wrapper();
    return fpast();
  endfunction

  task automatic tpast(output bit result);
    result = $past(data);
  endtask

  always @(posedge clk) begin
    cyc <= cyc + 1;
    data <= ~data;
    if (!offedge && cyc == 2) begin
      `checkd(fpast(), 1'b1);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  initial begin
    offedge = $test$plusargs("offedge") != 0;
    void'($value$plusargs("expect_past=%b", exp_past));
    if (offedge) begin
      #6;
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  final begin
    bit tres;
    `checkd($past(data), exp_past);
    `checkd(fpast_wrapper(), exp_past);
    tpast(tres);
    `checkd(tres, exp_past);
  end

endmodule
