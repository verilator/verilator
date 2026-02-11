// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module x;
  event a;
  event b;

  bit ok = 0;

  task do_the_job();
    static bit first = 1;
    if (first) begin
      first = 0;
      @a;
      ok = 1;
    end
    else begin
      ->a;
    end
  endtask

  initial begin
    #1 ->b;
    #100;
    if (!ok) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end
  always @b do_the_job();
  always @b do_the_job();
endmodule
