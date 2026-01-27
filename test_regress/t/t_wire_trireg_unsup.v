// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  trireg unsup;
  trireg (small) unsup_s;
  trireg (medium) unsup_m;
  trireg (large) unsup_l;

endmodule
