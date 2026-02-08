// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2025 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

module t_scope_std_randomize;
  bit [7:0] addr;
  bit [15:0] data;

  function bit run();
    int ready;
    int success;

    bit [7:0] old_addr;
    bit [15:0] old_data;
    int old_ready;

    old_addr = addr;
    old_data = data;
    old_ready = ready;
    success = randomize(addr, ready);  // std::randomize
    if (success == 0) return 0;
    if (addr == old_addr && data != old_data && ready == old_ready) begin
      return 0;
    end
    return 1;
  endfunction

  initial begin
    automatic bit ok = 0;
    int success;

    ok = 0;
    ok = run();
    if (!ok) $stop;

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
