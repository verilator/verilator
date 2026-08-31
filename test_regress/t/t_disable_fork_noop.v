// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); $stop; end while(0);
// verilog_format: on

module t;
  bit disabled_fork = 0;
  bit disabled_victim = 0;
  bit joined = 0;

  initial begin
    fork
      begin : victim
        disable fork;  // should be no-op
        disabled_fork=1;
        forever begin
          #1;
        end
      end
      begin
        #2;
        disable victim;
        disabled_victim=1;
      end
    join
    joined=1;
  end

  initial begin
    #1; #0;
    `checkd(disabled_fork, 1);
    `checkd(disabled_victim, 0);
    `checkd(joined, 0);
    #2; #0;
    `checkd(disabled_fork, 1);
    `checkd(disabled_victim, 1);
    `checkd(joined, 1);
    $info("*-* All Finished *-*");
    $finish;
  end
endmodule
