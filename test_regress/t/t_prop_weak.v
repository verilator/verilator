// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d: got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  int cyc = 0;
  event e;
  bit [7:0] hit = 0;

  always @(posedge clk) begin
    ++cyc;
    if (cyc < 5) begin
      ->e;
    end
    else begin
      `checkd(hit, 'b1111111);
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

  assert property (@(e) weak (##1 1 ##1 1));
  assert property (@(e) weak (1 ##1 1 ##1 1));
  assert property (@(e) weak (1 ##1 1));

  assert property (@(e) weak (##1 1 ##1 1)) begin
    hit |= 'b1;
  end
  assert property (@(e) weak (1 ##1 1 ##1 1)) begin
    hit |= 'b10;
  end
  assert property (@(e) weak (1 ##1 1)) begin
    hit |= 'b100;
  end

  assert property (@(e) weak (##1 1 ##1 0))
  else begin
    hit |= 'b1000;
  end
  assert property (@(e) weak (##1 0))
  else begin
    hit |= 'b10000;
  end
  assert property (@(e) weak (1 ##1 1 ##1 0))
  else begin
    hit |= 'b100000;
  end
  assert property (@(e) weak (1 ##1 0))
  else begin
    hit |= 'b1000000;
  end

endmodule
