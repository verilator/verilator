// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test: Soft cross-object constraints should respect IEEE 1800-2023 18.5.13
// outer-scope soft has higher priority than inner-scope soft.

class sub_cfg_c;
  rand int unsigned timeout;
  rand bit enabled;
  constraint soft_defaults {
    soft timeout == 1000;
    soft enabled == 0;
  }
endclass

class parent_cfg_c;
  rand bit enabled;
  rand sub_cfg_c sub_a;
  constraint soft_defaults { soft enabled == 0; }
  constraint propagate_cons {
    if (enabled) { sub_a.enabled == 1; }
  }
  function new();
    sub_a = new();
  endfunction
endclass

class top_test_c;
  rand parent_cfg_c cfg;
  rand sub_cfg_c extra_cfg;
  constraint cfg_hard_cons { cfg.enabled == 1; }
  constraint cfg_soft_cons {
    soft cfg.sub_a.timeout == 5000;
    soft extra_cfg.timeout == 9999;
    soft extra_cfg.enabled == 1;
  }
  function new();
    cfg = new();
    extra_cfg = new();
  endfunction
endclass

module t;
  initial begin
    static top_test_c obj = new();
    repeat (10) begin
      `checkd(obj.randomize(), 1)
      // Two-level cross-object soft: parent's soft overrides child's
      `checkd(obj.cfg.sub_a.timeout, 32'd5000)
      // One-level cross-object soft: parent's soft overrides child's
      `checkd(obj.extra_cfg.timeout, 32'd9999)
      `checkd(obj.extra_cfg.enabled, 1'b1)
      // Hard constraint propagation still works
      `checkd(obj.cfg.enabled, 1'b1)
      `checkd(obj.cfg.sub_a.enabled, 1'b1)
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
