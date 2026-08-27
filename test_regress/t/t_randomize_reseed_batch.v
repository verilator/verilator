// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// Reseeding with srandom() or set_randstate() must make randomize() reproducible
// regardless of what ran before, so a sampler caching solutions across calls has
// to drop them on either.

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  class C;
    rand bit [7:0] a;
    constraint c { a < 20; }
  endclass

  initial begin
    automatic C used = new;
    automatic C fresh = new;
    automatic int ok;
    // Only difference between the two: `used` has randomized before the reseed
    repeat (3) begin
      ok = used.randomize();
      `checkd(ok, 1);
    end
    used.srandom(42);
    fresh.srandom(42);
    ok = used.randomize();
    `checkd(ok, 1);
    ok = fresh.randomize();
    `checkd(ok, 1);
    `checkd(used.a, fresh.a);

    // Same again through get_randstate/set_randstate, which can restore the very
    // state the object already holds
    begin
      automatic C warm = new;
      automatic C cold = new;
      automatic string state;
      repeat (2) begin
        ok = warm.randomize();
        `checkd(ok, 1);
      end
      state = warm.get_randstate();
      warm.set_randstate(state);
      cold.set_randstate(state);
      ok = warm.randomize();
      `checkd(ok, 1);
      ok = cold.randomize();
      `checkd(ok, 1);
      `checkd(warm.a, cold.a);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
