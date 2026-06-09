// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  logic [1:0] sel;
  logic a;
  logic b;

  int linear_f = 0;
  int default_f = 0;
  int vacuous_f = 0;
  int delay_f = 0;

  always_comb begin
    sel = cyc[1:0];
    a = 1'b1;
    b = 1'b1;
  end

  property p_delay(logic [1:0] delay);
    case (delay)
      2'd0 : a && b;
      2'd1 : a ##2 b;
      2'd2 : a ##4 b;
      2'd3 : a ##8 b;
      default: 0;
    endcase
  endproperty

  property p_linear_search;
    case (sel)
      2'd0 : 1'b0;
      2'd0, 2'd1 : 1'b1;
      default 1'b1;
    endcase
  endproperty

  property p_default_ignored_during_search;
    case (sel)
      default: 1'b0;
      2'd2 : 1'b1;
    endcase
  endproperty

  property p_no_default_vacuous_success;
    case (sel)
      2'd0 : 1'b0;
    endcase
  endproperty

  property p_only_default;
    case (sel)
      default: 1'b1;
    endcase
  endproperty

  assert property (@(posedge clk) p_delay(sel)) else delay_f++;
  assert property (@(posedge clk) p_linear_search) else linear_f++;
  assert property (@(posedge clk) p_default_ignored_during_search) else default_f++;
  assert property (@(posedge clk) p_no_default_vacuous_success) else vacuous_f++;
  assert property (@(posedge clk) p_only_default) else `stop;

  always @(posedge clk) begin
    cyc <= cyc + 1;
  end

  always @(negedge clk) begin
    if (cyc == 16) begin
      `checkd(delay_f, 0);
      `checkd(linear_f, 4);
      `checkd(default_f, 12);
      `checkd(vacuous_f, 4);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
