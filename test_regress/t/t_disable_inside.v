// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkt(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0t exp=%0t (%t !== %t)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;
  initial begin
    static int x = 0;
    fork : fork_blk
      begin
        #1;
        disable fork_blk;  // Disables both forked processes
        $stop;
      end
      begin
        `checkt($time, 0);
        x = 1;
        #2;
        $stop;
      end
    join_none
    #1;
    if (x != 1) begin
      $display(x);
      $stop;
    end
  end

  initial begin
    static int y = 0;
    fork
      begin : fork_branch
        #1;
        disable fork_branch;  // Disables only this branch of the fork
        $stop;
      end
      begin
        `checkt($time, 0);
        y = 1;
        #2;
        `checkt($time, 2);
        y = 2;
      end
    join_none
    #1;
    if (y != 1) begin
      $display(y);
      $stop;
    end
    #1;
    if (y != 2) begin
      $display(y);
      $stop;
    end
  end

  initial begin
    fork : fork_blk2
      begin
        `checkt($time, 0);
        disable fork_blk2;
        $stop;
      end
      begin
        `checkt($time, 0);
        #1 $stop;
      end
    join_none
  end

  initial begin
    fork : fork_blk3
      begin
        `checkt($time, 0);
        #1 $stop;
      end
      begin
        `checkt($time, 0);
        disable fork_blk3;
        $stop;
      end
    join_none
  end

  initial begin
    fork : fork_blk4
      begin
        `checkt($time, 0);
        if ($c("false")) begin
          disable fork_blk4;
          $stop;
        end
        #1;
      end
      begin
        `checkt($time, 0);
        #1;
        `checkt($time, 1);
      end
    join_none
  end

  initial begin
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
