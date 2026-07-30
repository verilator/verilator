// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// A hierarchical disable of a named fork in one module instance must terminate
// only that instance's fork branch. IEEE 1800-2023 A.6.5 permits disable of a
// hierarchical_block_identifier.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module child (
    output bit survived,
    output bit done
);

  initial begin : init
    fork : fork_blk
      begin
        #5;
        survived = 1'b1;
      end
    join_none
    #6;
    done = 1'b1;
  end
endmodule

// This separate case disables a fork declared in a sibling module, rather than
// another instance of the source fork declaration.
module fork_target (
    output bit survived,
    output bit done
);

  initial begin : init
    fork : target_fork
      begin
        #5;
        survived = 1'b1;
      end
    join_none
    #6;
    done = 1'b1;
  end
endmodule

module disabler (
    output bit survived,
    output bit done
);

  initial begin
    fork : source_fork
      begin
        #2;
        disable t.target_inst.init.target_fork;
      end
      begin
        #4;
        survived = 1'b1;
      end
    join
    done = 1'b1;
  end
endmodule

module t;

  bit survived0;
  bit done0;
  bit survived1;
  bit done1;
  bit target_survived;
  bit target_done;
  bit disabler_survived;
  bit disabler_done;

  child child0 (
      .survived(survived0),
      .done(done0)
  );

  child child1 (
      .survived(survived1),
      .done(done1)
  );

  fork_target target_inst (
      .survived(target_survived),
      .done(target_done)
  );

  disabler disabler_inst (
      .survived(disabler_survived),
      .done(disabler_done)
  );

  initial begin
    #1;
    disable child0.init.fork_blk;
    #7;
    `checkd(done0, 1'b1);
    `checkd(done1, 1'b1);
    `checkd(survived0, 1'b0);
    `checkd(survived1, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #7;
    `checkd(target_done, 1'b1);
    `checkd(target_survived, 1'b0);
    `checkd(disabler_done, 1'b1);
    `checkd(disabler_survived, 1'b1);
  end
endmodule
