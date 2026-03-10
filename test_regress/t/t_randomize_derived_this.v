// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test: this.randomize() called in derived class with inherited rand members
// and constraints from base class. Verifies IS_RANDOMIZED propagation and
// membersel write_var fallback for ancestor classes.

class sub_cfg_c;
  rand bit enabled;
  constraint defaults {
    soft enabled == 1'b0;
  }
endclass

class base_c;
  rand sub_cfg_c cfg;
  rand int unsigned watchdog;

  constraint override_cons {
    cfg.enabled == 1'b1;
  }

  constraint watchdog_range {
    watchdog inside {[32'd50:32'd200]};
  }

  function new();
    cfg = new();
  endfunction
endclass

// Derived class: no additional rand members, calls this.randomize()
class derived_c extends base_c;
  function int do_randomize();
    return this.randomize();
  endfunction
endclass

// Deep inheritance: grandchild with no rand members
class grandchild_c extends derived_c;
  function int do_rand_deep();
    return this.randomize();
  endfunction
endclass

module t;
  initial begin
    automatic derived_c d = new();
    automatic grandchild_c g = new();

    // Test derived class this.randomize()
    repeat (20) begin
      `checkd(d.do_randomize(), 1)
      `checkd(d.cfg.enabled, 1)
      `checkd(d.watchdog >= 32'd50 && d.watchdog <= 32'd200, 1)
    end

    // Test deep inheritance this.randomize()
    repeat (20) begin
      `checkd(g.do_rand_deep(), 1)
      `checkd(g.cfg.enabled, 1)
      `checkd(g.watchdog >= 32'd50 && g.watchdog <= 32'd200, 1)
    end

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
