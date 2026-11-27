// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
  input clk,
  input clk2
);
  logic a, b_basic, b_after, c_after, c_3clk, b_switch, b_ack, c_ack, b_assert;

  cp_basic :
  cover property (@(posedge clk) a ##1 @(posedge clk2) b_basic);
  sequence s1;
    @(posedge clk) a ##1 @(posedge clk2) b_basic;
  endsequence
  cp_lrm :
  cover property (s1);
  cp_after :
  cover property (@(posedge clk) a ##1 @(posedge clk2) b_after ##1 c_after);
  cp_3clk :
  cover property (@(posedge clk) a ##1 @(posedge clk2) b_after ##1 @(posedge clk) c_3clk);
  cp_switch_back :
  cover property (@(posedge clk) a ##1 @(posedge clk2) ##1 ##1 @(posedge clk) ##1 b_switch);
  property cover_known_addr_ack;
    @(posedge clk)
    (
      $rose(a) |=>
      ##2 b_ack
      ##1 @(posedge clk2) ##1
      ##1 @(posedge clk) ##1 c_ack
    );
  endproperty : cover_known_addr_ack
  covprop_known_addr_ack :
  cover property (cover_known_addr_ack);
  cs_seq :
  cover sequence (@(posedge clk) a ##1 @(posedge clk2) b_basic);
  ap_switch_back :
  assert property (@(posedge clk) $rose(a) |=> ##1 @(posedge clk2) ##1 ##1 @(posedge clk)
                        ##1 b_assert);
endmodule
