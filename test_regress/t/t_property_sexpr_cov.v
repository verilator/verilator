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
`ifdef TEST_VERBOSE
    $display("cyc=%0d val=%0d", cyc, val);
`endif
    cyc <= cyc + 1;
    if (cyc == 100) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  cover property (@(e1) ##1 val[0])
    $display("[%0t] cover property, fileline:%0d", $time, `__LINE__);

  cover property (@(e2) not ##1 val[1])
    $display("[%0t] not cover property, fileline:%0d", $time, `__LINE__);

  cover property (@(posedge clk) ##3 val[0] && val[1])
    $display("[%0t] concurrent cover, fileline:%0d", $time, `__LINE__);
endmodule
