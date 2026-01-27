// DESCRIPTION: Verilator: Verilog Test module for SystemVerilog 'alias'
//
// Simple bi-directional alias test.
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2020 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

   initial begin
      int q[$];
      int qv[$];  // Value returns
      q = '{1, 2, 2, 4, 3};

      qv = q.find with (itemm == 2);

      qv = q.find(misspelled) with (misspelledd == 2);
   end

endmodule
