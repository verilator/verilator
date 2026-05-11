// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Packet;
  rand int m_dyn_arr[];
  rand int m_unp_arr[10];
  rand struct {int y;} m_struct;
endclass

module t;
  initial begin
    automatic Packet p = new;
    p.m_dyn_arr[0].rand_mode(0);
    p.m_unp_arr[0].rand_mode(0);
    p.m_struct.y.rand_mode(0);
  end
endmodule
