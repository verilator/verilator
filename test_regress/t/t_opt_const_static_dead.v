// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Static variables declared in code that never executes still exist, and can
// be referenced hierarchically, so they must not be deleted together with the
// dead code.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  // Branch of a constant if
  initial begin : init_if
    if (0) begin : blk
      static int x = 1;
      x = 10;
    end
  end

  // Body of a loop with a constant false condition
  initial begin : init_while
    while (0) begin : blk
      static int x = 2;
      x = 20;
    end
  end

  // After a disable
  initial begin : init_disable
    begin : outer
      disable outer;
      begin : blk
        static int x = 3;
        x = 30;
      end
    end
  end

  // After a break
  initial begin : init_break
    forever begin : body
      break;
      begin : blk
        static int x = 4;
        x = 40;
      end
    end
  end

  // Identical trailing blocks in both branches, each with its own static
  int last;
  initial begin : init_same
    for (int i = 0; i < 4; ++i) begin
      if (i[0]) begin
        static int x = 0;
        x = x + 1;
        last = x;
      end
      else begin
        static int x = 0;
        x = x + 1;
        last = x;
      end
    end
  end

  sub sub ();

  initial begin
    // After the other initial blocks
    #0;
    `checkd(init_if.blk.x, 1);
    `checkd(init_while.blk.x, 2);
    `checkd(init_disable.outer.blk.x, 3);
    `checkd(init_break.body.blk.x, 4);
    `checkd(last, 2);
    $finish;
  end

endmodule

module sub;
  final begin
    `checkd(t.init_if.blk.x, 1);
    `checkd(t.init_while.blk.x, 2);
    `checkd(t.init_disable.outer.blk.x, 3);
    `checkd(t.init_break.body.blk.x, 4);
    // Each branch ran twice, so its own static counted to 2
    `checkd(t.last, 2);
    $write("*-* All Finished *-*\n");
  end
endmodule
