// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2022-2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  bit clk = 0;
  initial forever #1 clk = ~clk;

  localparam MAX = 3;
  integer cyc = 1;

  property p_ev;
    eventually[2: 5] clk;
  endproperty

  property p_s_ev_alw;
    s_eventually always[2: 5] clk;
  endproperty

`ifdef PARSING_TIME
  property p_s_ev;
    s_eventually[2: 5] clk;
  endproperty

  property p_s_alw_ev;
    always s_eventually[2: 5] clk;
  endproperty

  assert property (@(posedge clk) p_s_ev);
  assert property (@(posedge clk) p_s_alw_ev);
`endif

  sequence delayed; 1 ##1 1; endsequence

  assert property (@(posedge clk) s_eventually delayed);
  assert property (@(posedge clk) eventually[1: 2] delayed);

  assert property (@(posedge clk) s_eventually ##1 1);
  assert property (@(negedge clk) s_eventually ##1 1);
  assert property (@(negedge clk) p_s_ev_alw);
  assert property (@(posedge clk) s_eventually (not (clk ##1 clk)));

  assert property (@(posedge clk) p_ev);
  always @(posedge clk) assert property (eventually[1: 2] clk);

  // Temporal if/case outcomes remain unsupported with pass actions, cover, or negation.
  assert property (@(posedge clk) if (cyc == 1) s_eventually (cyc >= 2) else 1'b1)
    $display("pass if");
  assert property (@(posedge clk) case (cyc) 1: s_eventually (cyc >= 2); default: 1'b1;
  endcase)
    $display("pass case");
  cover property (@(posedge clk) if (cyc == 1) s_eventually (cyc >= 2) else 1'b1);
  assert property (@(posedge clk) not (if (cyc == 1) s_eventually (cyc >= 2) else 1'b1));

`ifdef WIDTH_TIME
  assert property (@(posedge clk) eventually[32'h8000_0000: 32'h8000_0000] 1'b1);
  assert property (@(posedge clk) eventually[0: 64'h1_0000_0000] 1'b1);
`endif

  always @(posedge clk) begin
    ++cyc;
    if (cyc == MAX) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
