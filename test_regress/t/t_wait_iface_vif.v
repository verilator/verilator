// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off ZERODLY

interface my_if ();
  logic clk;
  realtime clk_period;
  bit clk_active = 0;

  initial begin
    wait (clk_active);
    forever begin
      #(clk_period);
      if (clk_active) begin
        case (clk)
          1'b0: clk = 1'b1;
          default: clk = 1'b0;
        endcase
      end
    end
  end

  // always @* with process::self() must not become a spinning coroutine
  always @* begin
    if (clk_active && clk_period == 0.0) begin
      automatic process p = process::self();
      $display("%m: active with 0 period (proc=%p)", p);
      $stop;
    end
  end

  function void set_period(realtime p);
    clk_period = p;
  endfunction

  function void start_clk();
    if (clk_period) clk_active = 1;
  endfunction
endinterface

class Driver;
  virtual my_if vif;

  task run();
    vif.set_period(5);
    #10;
    vif.start_clk();
  endtask
endclass

module t;
  my_if intf ();

  // Verify combinational always with timing controls still works as coroutine
  int combo_timing_count = 0;
  always @* begin
    combo_timing_count = combo_timing_count + 1;
    #1;
  end

  initial begin
    automatic Driver d = new;
    d.vif = intf;
    d.run();
    repeat (4) @(posedge intf.clk);
    if (combo_timing_count == 0) $stop;
    $write("*-* All Finished *-*\n");
    $finish;
  end

  initial begin
    #1000;
    $display("TIMEOUT");
    $stop;
  end
endmodule
