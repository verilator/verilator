// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

package uvm_pkg;
class uvm_queue #(type T=int);
endclass
class m_uvm_waiter;
endclass
class uvm_config_db#(type T=int);
  static local uvm_queue#(m_uvm_waiter) m_waiters[string];
  static function void set(int a, string b, string c, int d);
  endfunction
endclass
endpackage
package sfr_agent_pkg;
class sfr_monitor_abstract;
endclass
endpackage: sfr_agent_pkg
module sfr_monitor_bfm  #(ADDR_WIDTH = 8,
                          DATA_WIDTH = 8)
                        (
                         input [ADDR_WIDTH-1:0] address);
  import uvm_pkg::*;
  import sfr_agent_pkg::*; int SFR_MONITOR;
initial begin
  uvm_config_db #(sfr_monitor_abstract)::set(null, "uvm_test_top", "SFR_MONITOR", SFR_MONITOR);
end
endmodule: sfr_monitor_bfm
module hdl_top;
parameter DATA_WIDTH = 32;
parameter ADDR_WIDTH = 32;
sfr_monitor_bfm #(.ADDR_WIDTH(ADDR_WIDTH),
                  .DATA_WIDTH(DATA_WIDTH)) SFR_MONITOR(
                                                        .address(42));
endmodule
