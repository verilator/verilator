// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t (
    input clk
);
  integer cyc = 0;
  logic src_1 = 0;
  logic [7:0] src_8 = 8'h10;
  logic dst_1  /* verilator forceable */;
  logic [7:0] dst_8  /* verilator forceable */;

  always @* dst_1 = src_1;
  always @* dst_8 = src_8;

  always @(posedge clk) begin
    cyc <= cyc + 1;
    case (cyc)
      0: begin
        force dst_1 = src_1;
        force dst_8 = src_8 ^ 8'hf0;
        `checkh(dst_1, 1'b0);
        `checkh(dst_8, 8'he0);
      end
      1: begin
        release dst_1;
        release dst_8;
        src_1 = 1'b1;
        src_8 = 8'h23;
      end
      2: begin
        `checkh(dst_1, 1'b1);
        `checkh(dst_8, 8'h23);
        $write("*-* All Finished *-*\n");
        $finish;
      end
      default: begin
      end
    endcase
  end
endmodule
