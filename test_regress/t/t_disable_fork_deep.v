// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Disabling a named fork from a deeply nested sub-fork branch must terminate
// every process spawned within that fork, at all nesting levels, including
// branches suspended on a delay. Previously this crashed Verilator: the bail-out
// jump emitted for the disable targeted the outer fork branch and crossed a
// coroutine boundary once the nested forks were split into separate functions.
// Even disregarding the crash, processes of nested sub-forks were not registered
// for the kill, so a nested sibling survived and its $stop fired.
//
// The disable must also let the process that owns the disabled fork's 'join'
// resume after the join (IEEE 1800-2023 9.6.2): once the block is terminated,
// execution continues at the point after it. The *_resumed bits below latch that
// the parent ran past its join; a hang there leaves the bit clear and is caught
// at the end. A fork branch that itself holds a nested fork is killed while
// suspended at the inner join, so it must register a kill hook on its parent
// fork or the parent join counter is never decremented and the parent hangs.

// verilog_format: off
`define stop $stop
`define checkt(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0t exp=%0t (%t !== %t)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit d2_resumed = 1'b0;
  bit d3_resumed = 1'b0;
  bit d2a_resumed = 1'b0;
  bit d2r_resumed = 1'b0;
  bit ja1_resumed = 1'b0;

  // fork..join nested two levels: disabling the outer named fork from inside the
  // inner fork must kill the inner delayed sibling and the outer delayed sibling.
  initial begin
    fork : fork_d2
      begin
        fork
          begin
            `checkt($time, 0);
            disable fork_d2;
            $stop;
          end
          begin
            `checkt($time, 0);
            #1 $stop;
          end
        join
      end
      begin
        `checkt($time, 0);
        #1 $stop;
      end
    join
    `checkt($time, 0);
    d2_resumed = 1'b1;
  end

  // fork..join nested three levels: disabling the outermost named fork from the
  // innermost branch must kill the delayed siblings at every level.
  initial begin
    fork : fork_d3
      begin
        fork
          begin
            fork
              begin
                `checkt($time, 0);
                disable fork_d3;
                $stop;
              end
              begin
                `checkt($time, 0);
                #1 $stop;
              end
            join
          end
          begin
            `checkt($time, 0);
            #1 $stop;
          end
        join
      end
      begin
        `checkt($time, 0);
        #1 $stop;
      end
    join
    `checkt($time, 0);
    d3_resumed = 1'b1;
  end

  // fork..join_any nested two levels.
  initial begin
    fork : fork_d2a
      begin
        fork
          begin
            `checkt($time, 0);
            disable fork_d2a;
            $stop;
          end
          begin
            `checkt($time, 0);
            #1 $stop;
          end
        join_any
      end
      begin
        `checkt($time, 0);
        #1 $stop;
      end
    join_any
    `checkt($time, 0);
    d2a_resumed = 1'b1;
  end

  // fork..join_none nested two levels.
  initial begin
    fork : fork_d2n
      begin
        fork
          begin
            `checkt($time, 0);
            disable fork_d2n;
            $stop;
          end
          begin
            `checkt($time, 0);
            #1 $stop;
          end
        join_none
      end
      begin
        `checkt($time, 0);
        #1 $stop;
      end
    join_none
  end

  // fork..join nested two levels, but the disabling branch comes after the
  // delayed sibling (in source order) at both levels.
  initial begin
    fork : fork_d2r
      begin
        `checkt($time, 0);
        #1 $stop;
      end
      begin
        fork
          begin
            `checkt($time, 0);
            #1 $stop;
          end
          begin
            `checkt($time, 0);
            disable fork_d2r;
            $stop;
          end
        join
      end
    join
    `checkt($time, 0);
    d2r_resumed = 1'b1;
  end

  // fork..join_any whose only branch holds the nested fork that gets disabled.
  // join_any needs one branch to complete, but the only branch is killed while
  // suspended at its inner join, so the parent resumes only if that branch
  // decrements the join counter on kill.
  initial begin
    fork : fork_ja1
      begin
        fork
          begin
            `checkt($time, 0);
            disable fork_ja1;
            $stop;
          end
          begin
            `checkt($time, 0);
            #1 $stop;
          end
        join
      end
    join_any
    `checkt($time, 0);
    ja1_resumed = 1'b1;
  end

  initial begin
    #10;
    `checkd(d2_resumed, 1'b1);
    `checkd(d3_resumed, 1'b1);
    `checkd(d2a_resumed, 1'b1);
    `checkd(d2r_resumed, 1'b1);
    `checkd(ja1_resumed, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
