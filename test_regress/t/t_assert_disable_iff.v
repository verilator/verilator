// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Peter Monsson.
// SPDX-License-Identifier: CC0-1.0

module t (  /*AUTOARG*/
    // Inputs
    clk
);

  input clk;
  int cyc;

  Test test (  /*AUTOINST*/
      // Inputs
      .clk(clk),
      .cyc(cyc)
  );

  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 10) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule

module Test (
    input clk,
    input int cyc
);

`ifdef FAIL_ASSERT_1
  assert property (@(posedge clk) disable iff (0) 0)
  else $display("wrong disable");
`endif

  assert property (@(posedge clk) disable iff (1) 0) $stop;
  else $stop;

  assert property (@(posedge clk) disable iff (1) 1) $stop;
  else $stop;

  assert property (@(posedge clk) disable iff (0) 1);

  // Pass 1st cycle
  assert property (@(cyc) disable iff (cyc != $sampled(cyc)) cyc == 0);

  //
  // Cover properties behave differently
  //

  cover property (@(posedge clk) disable iff (1) 1) $stop;

  cover property (@(posedge clk) disable iff (1) 0) $stop;

  cover property (@(posedge clk) disable iff (0) 1) $display("*COVER: ok");

  cover property (@(posedge clk) disable iff (0) 0) $stop;

endmodule
