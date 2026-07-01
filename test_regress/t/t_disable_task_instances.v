// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Disabling a module task by its local name in one module instance must not
// terminate the same task declaration's activation in another module instance.
// Each module instance and task definition creates a distinct hierarchical scope.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module child (
    input bit do_disable,
    output bit survived,
    output bit done
);

  task automatic run();
    #5;
    survived = 1'b1;
  endtask

  initial begin
    fork
      run();
    join_none
    if (do_disable) begin
      #1;
      disable run;
    end
    else begin
      #6;
    end
    done = 1'b1;
  end
endmodule
module t;

  bit survived0;
  bit done0;
  bit survived1;
  bit done1;

  child child0 (
      .do_disable(1'b1),
      .survived(survived0),
      .done(done0)
  );

  child child1 (
      .do_disable(1'b0),
      .survived(survived1),
      .done(done1)
  );

  initial begin
    #8;
    `checkd(done0, 1'b1);
    `checkd(done1, 1'b1);
    `checkd(survived0, 1'b0);
    `checkd(survived1, 1'b1);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
