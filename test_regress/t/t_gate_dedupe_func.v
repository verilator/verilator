// DESCRIPTION: Verilator: Gate deduplication through function argument
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jose Tejada
// SPDX-License-Identifier: CC0-1.0

module game_test(output [7:0] st_dout);
  jtcop_game_sdram u_game(
    .snd_vu(),
    .snd_peak(),
    .st_dout(st_dout)
  );
endmodule

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
  reg [15:0] hscr;
  reg [15:0] vscr;
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
    if (rst) begin
      vscr <= {def_cfg[7], def_cfg[6]};
    end else begin
      case (cpu_addr[2:1])
        0: hscr <= combine(hscr);
        1: vscr <= combine(vscr);
        2: colscr_sh <= cpu_dout[3:0];
        3: rowscr_sh <= cpu_dout[3:0];
      endcase
    end
  end
endmodule

module jtcop_game(
    input clk,
    input [7:0] st_addr,
    output [7:0] st_dout,
    output [13:1] ba2mcu_addr,
    output [18:1] main_addr
);
  wire [7:0] st_snd;
  reg [7:0] st_mux;
  assign st_dout = st_mux;

  always @(posedge clk) begin
    case (st_addr[7:6])
      0: st_mux <= st_main;
      1: st_mux <= st_snd;
      2: st_mux <= snd_latch;
      3: st_mux <= std_video;
    endcase
  end

  jtcop_main u_main(
    .snd_latch(snd_latch),
    .cpu_addr(main_addr),
    .st_dout(st_main)
  );
  jtcop_video u_video(
    .game_id(game_id),
    .cpu_addr(main_addr[12:1]),
    .mcu_addr(ba2mcu_addr[10:1]),
    .prisel(prisel),
    .st_addr(sta_video),
    .st_dout(std_video)
  );
  jtcop_sdram u_sdram(.game_id(game_id));
endmodule

module jtcop_main(
    output [18:1] cpu_addr,
    output reg [7:0] snd_latch,
    output reg [7:0] st_dout
);
  assign cpu_dout = 0,
         cpu_addr = 0,
         UDSWn = 1,
         LDSWn = 1,
         RnW = 0,
         sec = 0,
         pal_cs = 0,
         fmode_cs = 0,
         fsft_cs = 0,
         fmap_cs = 0,
         bmode_cs = 0,
         bsft_cs = 0,
         bmap_cs = 0,
         cmode_cs = 0,
         csft_cs = 0,
         cmap_cs = 0,
         huc_cs = 0,
         obj_cs = 0,
         obj_copy = 0,
         ram_cs = 0,
         rom_cs = 0;
endmodule

module jtcop_sdram(output reg [1:0] game_id = 0);
endmodule

module jtcop_video(
    input [1:0] game_id,
    input [12:1] cpu_addr,
    input [9:0] mcu_addr,
    input [7:0] prisel,
    input [7:0] st_addr,
    output reg [7:0] st_dout
);
  localparam [1:0] HIPPODROME = 2'd1;
  wire [7:0] st_dout0, st_dout1;

  always @(posedge clk) begin
    case (st_addr[5:4])
      0: st_dout <= st_dout0;
      1: st_dout <= st_dout1;
      2: st_dout <= st_dout2;
      3: st_dout <= prisel;
    endcase
  end

  assign ba2_addr = game_id == HIPPODROME ? {2'd0, mcu_addr} : cpu_addr;
  jtcop_bac06 u_ba2(
    .rst(rst),
    .clk(clk),
    .cpu_dout(ba2_din),
    .cpu_addr(ba2_addr),
    .cpu_dsn(ba2_dsn),
    .st_addr(st_addr),
    .st_dout(st_dout2)
  );
endmodule

module jtcop_game_sdram(
    output [7:0] st_dout,
    output [5:0] snd_vu,
    output snd_peak
);
  jtcop_game u_game(
    .clk(clk),
    .ba2mcu_addr(ba2mcu_addr),
    .main_addr(main_addr),
    .st_addr(st_addr),
    .st_dout(st_dout)
  );
endmodule
