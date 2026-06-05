// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Wilson Snyder.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test the graceful-degradation safety net for embedded covergroups (the dominant
// UVM pattern: a covergroup declared inside a class whose coverpoints reference the
// enclosing object's members).  Such a covergroup is lowered into a sibling class
// with no handle to the enclosing instance, so emitting it would produce
// uncompilable C++ ("invalid use of non-static data member").  Until the enclosing
// back-pointer feature exists, Verilator must emit a clean COVERIGN warning and skip
// lowering the covergroup, rather than crashing the C++ compile.

class ubus_transfer;
  bit [15:0] addr;
  bit read_write;
endclass

class ubus_master_monitor;
  ubus_transfer trans_collected;

  // Coverpoints reference 'trans_collected', a member of the enclosing class.
  // A cross is included so the safety-net cleanup also exercises cross removal.
  covergroup cov_trans;
    trans_start_addr : coverpoint trans_collected.addr {option.auto_bin_max = 16;}
    trans_dir        : coverpoint trans_collected.read_write;
    trans_addr_x_dir : cross trans_start_addr, trans_dir;
  endgroup

  function new();
    trans_collected = new;
    cov_trans = new;
  endfunction
endclass

module t;
  ubus_master_monitor m;
  initial begin
    m = new;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
