// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Disabling a named fork..join / fork..join_any block from one of its own
// branches must terminate the sibling branches, including any that are
// suspended on a delay. This is the join/join_any analogue of the
// fork..join_none cases in t_disable_inside (#6591): the bug was that a sibling
// spawned later in source order registered its process for kill only after the
// disabling branch had already issued the kill, so the sibling survived and its
// $stop fired one time unit later.

// verilog_format: off
`define stop $stop
`define checkt(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0t exp=%0t (%t !== %t)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  // fork..join: the disabling branch comes first, the delayed sibling second.
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
    join
  end

  // fork..join: the delayed sibling comes first, the disabling branch second.
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
    join
  end

  // fork..join: the delayed sibling also contains an unreachable disable, which
  // makes LinkJump wrap its registration in a JumpBlock. It must still register
  // before the synthetic fork-start delay so the earlier disable kills it.
  initial begin
    fork : fork_blk_wrap
      begin
        `checkt($time, 0);
        disable fork_blk_wrap;
        $stop;
      end
      begin
        `checkt($time, 0);
        #1;
        if ($c("false")) disable fork_blk_wrap;
        $stop;
      end
    join
  end

  // fork..join_any: the disabling branch comes first, the delayed sibling second.
  initial begin
    fork : fork_blk2a
      begin
        `checkt($time, 0);
        disable fork_blk2a;
        $stop;
      end
      begin
        `checkt($time, 0);
        #1 $stop;
      end
    join_any
  end

  // fork..join_any: the delayed sibling comes first, the disabling branch second.
  initial begin
    fork : fork_blk3a
      begin
        `checkt($time, 0);
        #1 $stop;
      end
      begin
        `checkt($time, 0);
        disable fork_blk3a;
        $stop;
      end
    join_any
  end

  // fork..join_any: the delayed sibling's own unreachable disable again forces a
  // JumpBlock wrapper around its registration.
  initial begin
    fork : fork_blk_wrap_any
      begin
        `checkt($time, 0);
        disable fork_blk_wrap_any;
        $stop;
      end
      begin
        `checkt($time, 0);
        #1;
        if ($c("false")) disable fork_blk_wrap_any;
        $stop;
      end
    join_any
  end

  // fork..join that can be disabled, but takes the path where disable is not
  // reached: both branches must run to completion with their timing intact.
  initial begin
    fork : fork_blk4
      begin
        `checkt($time, 0);
        if ($c("false")) begin
          disable fork_blk4;
          $stop;
        end
        #1;
        `checkt($time, 1);
      end
      begin
        `checkt($time, 0);
        #1;
        `checkt($time, 1);
      end
    join
  end

  // Deeply nested fork..join: the named fork is several levels deep inside other
  // forks and one of its own branches disables it. The delayed sibling at that
  // deep level must still be killed, so the fix has to work when the disable-able
  // fork is itself nested inside other (suspending) forks.
  initial begin
    fork
      begin
        fork
          begin
            fork : fork_deep
              begin
                `checkt($time, 0);
                disable fork_deep;
                $stop;
              end
              begin
                `checkt($time, 0);
                #1 $stop;
              end
            join
          end
        join
      end
    join
  end

  initial begin
    #10;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
