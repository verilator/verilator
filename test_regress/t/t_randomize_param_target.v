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

// IEEE 1800-2023 18.7: an undotted name in 'randomize() with' first resolves
// in the randomized object's class, falling back to the caller's scope only
// if absent there. When the target is a parameterized class, its scope is
// unavailable until V3Param specialization, so the whole constraint must be
// deferred rather than resolved (or errored) up front. The call below sits
// in an extern-defined task body, as in the original report.

class item;
  rand int unsigned driver_delay;
endclass

class generic_sequence #(type T = item);
  rand T cmd;
  rand int unsigned mode;
  function new();
    cmd = new;
  endfunction
endclass

class outer_sequence;
  extern task body();
endclass

task outer_sequence::body();
  generic_sequence#(item) seq;
  item cmd;  // Caller-scope 'cmd' for the local:: check below
  int ok;
  seq = new;
  cmd = new;

  // Undotted 'cmd' reaches the randomized object's member, not caller scope.
  ok = seq.randomize() with {
    cmd.driver_delay inside {[0:100]};
  };
  `checkd(ok, 1)
  if (seq.cmd.driver_delay > 100) begin
    $write("%%Error: driver_delay=%0d exceeds 100\n", seq.cmd.driver_delay);
    `stop;
  end

  // Bare undotted member of the parameterized target.
  ok = seq.randomize() with {
    mode == 9;
  };
  `checkd(ok, 1)
  `checkd(seq.mode, 9)

  // Explicit 'this' means the randomized object.
  ok = seq.randomize() with {
    this.cmd.driver_delay == 7;
  };
  `checkd(ok, 1)
  `checkd(seq.cmd.driver_delay, 7)

  // 'local::' forces caller scope: bound to the local handle's value.
  // The +1 keeps this from passing as a tautology when misbound: binding
  // either side to the wrong 'cmd' makes the constraint unsatisfiable.
  cmd.driver_delay = 42;
  ok = seq.randomize() with {
    cmd.driver_delay == local::cmd.driver_delay + 1;
  };
  `checkd(ok, 1)
  `checkd(seq.cmd.driver_delay, 43)
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
