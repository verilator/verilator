// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// 'randomize() with' on a parameterized class target (IEEE 1800-2023 18.7)

class item;
  rand int unsigned driver_delay;
endclass

class fast_item;
  rand int unsigned driver_delay;
endclass

class generic_sequence #(
    type T = item
);
  rand T cmd;
  rand int unsigned mode;
  function new();
    cmd = new;
  endfunction
  function int unsigned limit();
    return 100;
  endfunction
endclass

class outer_sequence;
  extern task body();
endclass

task outer_sequence::body();
  generic_sequence #(item) seq;
  generic_sequence #(fast_item) fseq;
  item cmd;  // Caller-scope 'cmd' for the local:: check below
  int ok;
  seq = new;
  fseq = new;
  cmd = new;

  // A second specialization of the same generic class resolves independently.
  ok = fseq.randomize() with {cmd.driver_delay == 11;};
  `checkd(ok, 1)
  `checkd(fseq.cmd.driver_delay, 11)

  // Undotted 'cmd' reaches the randomized object's member, not caller scope.
  ok = seq.randomize() with {cmd.driver_delay inside {[0 : 100]};};
  `checkd(ok, 1)
  if (seq.cmd.driver_delay > 100) begin
    $write("%%Error: driver_delay=%0d exceeds 100\n", seq.cmd.driver_delay);
    `stop;
  end

  // Bare undotted member of the parameterized target.
  ok = seq.randomize() with {mode == 9;};
  `checkd(ok, 1)
  `checkd(seq.mode, 9)

  // Explicit 'this' means the randomized object.
  ok = seq.randomize() with {this.cmd.driver_delay == 7;};
  `checkd(ok, 1)
  `checkd(seq.cmd.driver_delay, 7)

  // Method call binds to the target's method.
  ok = seq.randomize() with {
    cmd.driver_delay <= limit();
    mode == 3;
  };
  `checkd(ok, 1)
  `checkd(seq.mode, 3)
  if (seq.cmd.driver_delay > 100) begin
    $write("%%Error: driver_delay=%0d exceeds 100\n", seq.cmd.driver_delay);
    `stop;
  end

  // 'local::' forces caller scope; +1 makes a misbind unsatisfiable.
  cmd.driver_delay = 42;
  ok = seq.randomize() with {cmd.driver_delay == local:: cmd.driver_delay + 1;};
  `checkd(ok, 1)
  `checkd(seq.cmd.driver_delay, 43)

  // Target declared without #(), so the default specialization (IEEE 1800-2023 8.25).
  begin
    generic_sequence dseq = new;
    cmd.driver_delay = 20;
    ok = dseq.randomize() with {
      cmd.driver_delay == local::cmd.driver_delay + 1;
      mode == limit();
    };
    `checkd(ok, 1)
    `checkd(dseq.cmd.driver_delay, 21)
    `checkd(dseq.mode, 100)
  end
endtask

module t;
  outer_sequence outer;
  initial begin
    outer = new;
    outer.body();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
