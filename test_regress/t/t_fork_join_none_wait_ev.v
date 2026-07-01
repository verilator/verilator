// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
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
  int cnt = 0;
  event ev[128];

  always @(posedge clk) begin
    ++cyc;
    if (cyc >= 3) begin
      `checkd(cnt, 128);
      $finish;
    end
  end

  for (genvar i = 0; i < 128; ++i) begin : gen_ev_wait
    always @(posedge clk) begin
      if (cyc < 3) begin
        fork
          begin
            ->ev[i];
            @(ev[i]);
            cnt++;
          end
        join_none
      end
    end
  end
endmodule
