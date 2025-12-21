// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

module t;
  initial begin
    int x = 0;
    fork : fork_blk
      begin
        #1;
        disable fork_blk;  // Disables both forked processes
        $stop;
      end
      begin
        if ($time != 0) $stop;
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
    int y = 0;
    fork
      begin : fork_branch
        #1;
        disable fork_branch;  // Disables only this branch of the fork
        $stop;
      end
      begin
        if ($time != 0) $stop;
        y = 1;
        #2;
        if ($time != 2) $stop;
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

  // TODO: This doesn't work due to the second fork branch not being added to
  //       the killQueue when the 'disable' is executed with no delay after
  //       the fork starts. See the case below which is the same, but the
  //       fork branches are in the opposite order so it happens to work.
  //initial begin
  //  fork : fork_blk2
  //    begin
  //      if ($time != 0) $stop;
  //      disable fork_blk2;
  //      $stop;
  //    end
  //    begin
  //      if ($time != 0) $stop;
  //      #1 $stop;
  //    end
  //  join_none
  //end

  initial begin
    fork : fork_blk3
      begin
        if ($time != 0) $stop;
        #1 $stop;
      end
      begin
        if ($time != 0) $stop;
        disable fork_blk3;
        $stop;
      end
    join_none
  end

  initial begin
    fork : fork_blk4
      begin
        if ($time != 0) $stop;
        if ($c("false")) begin
          disable fork_blk4;
          $stop;
        end
        #1;
      end
      begin
        if ($time != 0) $stop;
        #1;
        if ($time != 1) $stop;
      end
    join_none
  end

  initial begin
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
