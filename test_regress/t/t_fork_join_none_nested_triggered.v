// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro Ltd
// SPDX-License-Identifier: CC0-1.0

module test;
  mailbox #(int) mbox;
  initial begin
    mbox = new();

    fork
      repeat (2) begin
        int val;
        mbox.get(val);
        fork
          fork
            begin
              $finish;
            end
          join_none
        join_none
      end
    join_none

    mbox.put(1);
    #1;
    $stop;
  end
endmodule
