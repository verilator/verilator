// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// $past in 'final' for on-tick and between-tick simulation ends

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
      if (fpast() !== 1'b1) begin
        $display("%%Error: wrong $past in function at tick: got=%0b exp=1", fpast());
        $stop;
      end
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
    if ($past(data) !== exp_past) begin
      $display("%%Error: wrong $past in final: got=%0b exp=%0b offedge=%0b", $past(data), exp_past,
               offedge);
      $stop;
    end
    if (fpast_wrapper() !== exp_past) begin
      $display("%%Error: wrong $past via function in final: got=%0b exp=%0b offedge=%0b",
               fpast_wrapper(), exp_past, offedge);
      $stop;
    end
    tpast(tres);
    if (tres !== exp_past) begin
      $display("%%Error: wrong $past via task in final: got=%0b exp=%0b offedge=%0b", tres,
               exp_past, offedge);
      $stop;
    end
  end

endmodule
