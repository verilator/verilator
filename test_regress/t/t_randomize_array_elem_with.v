// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class mbus_seq_item;
  rand logic MREAD;
endclass

module t;
  initial begin
    mbus_seq_item req_c[10];
    for (int i = 0; i < 10; i++) begin
      req_c[i] = new;

      if (req_c[i].randomize() with {MREAD == 0;} == 0) begin
        $stop;
      end
      if (req_c[i].MREAD != 0) begin
        $stop;
      end

      if (req_c[i].randomize() == 0) begin
        $stop;
      end

      req_c[i].srandom(42);
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
