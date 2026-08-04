// DESCRIPTION: Verilator: Gate deduplication through function argument
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jose Tejada
// SPDX-License-Identifier: CC0-1.0

module jtcop_bac06(
    input rst,
    input clk,
    input [15:0] cpu_dout,
    input [12:1] cpu_addr,
    input [1:0] cpu_dsn,
    input [7:0] st_addr,
    output reg [7:0] st_dout
);
  reg [7:0] mode[0:3];
  reg [15:0] hscr, vscr;
  reg [3:0] colscr_sh, rowscr_sh;
  reg [7:0] def_cfg[0:15];

  always @(posedge clk) begin
    case (st_addr[3:0])
      0, 1, 2, 3: st_dout <= mode[st_addr[1:0]];
      4: st_dout <= hscr[7:0];
      5: st_dout <= hscr[15:8];
      6: st_dout <= vscr[7:0];
      7: st_dout <= vscr[15:8];
      8: st_dout <= {colscr_sh, rowscr_sh};
      default: st_dout <= '0;
    endcase
  end

  function [15:0] combine(input [15:0] din);
    combine = {cpu_dsn[1] ? din[15:8] : cpu_dout[15:8],
               cpu_dsn[0] ? din[7:0] : cpu_dout[7:0]};
  endfunction

  always @(posedge clk) begin
    if (rst) vscr <= {def_cfg[7], def_cfg[6]};
    else case (cpu_addr[2:1])
      0: hscr <= combine(hscr);
      1: vscr <= combine(vscr);
      2: colscr_sh <= cpu_dout[3:0];
      3: rowscr_sh <= cpu_dout[3:0];
    endcase
  end
endmodule

module jtcop_game(input clk, output [7:0] st_dout);
  wire [12:1] cpu_addr;
  jtcop_main u_main(.cpu_addr(cpu_addr));
  jtcop_video u_video(.cpu_addr(cpu_addr), .st_dout(st_dout));
endmodule

module jtcop_main(output [12:1] cpu_addr);
  assign cpu_addr = '0;
endmodule

module jtcop_video(
    input [12:1] cpu_addr,
    output reg [7:0] st_dout
);
  jtcop_bac06 u_ba2(.rst(rst), .clk(clk), .cpu_dout(ba2_din),
                    .cpu_addr(cpu_addr), .cpu_dsn(ba2_dsn), .st_addr(st_addr),
                    .st_dout(st_dout));
endmodule
