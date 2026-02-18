// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro Ltd.
// SPDX-License-Identifier: CC0-1.0

module test;
  mailbox #(int) mbox;
  initial begin
    mbox = new();
    mbox.put(10);
    mbox.put(30);

    repeat(2) begin
      int item;
      mbox.get(item);
      fork
        begin
          $display("got", item);
          if(item==10)
            $finish;
        end
      join_none
    end

    #0;
    $stop;
  end
endmodule
