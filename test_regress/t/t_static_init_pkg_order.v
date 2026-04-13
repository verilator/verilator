// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 PlanV GmbH
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test package static init ordering with cross-package side effects.
// Mirrors the UVM factory pattern (uvm_coreservice_t / uvm_init).

package pkg_a;
  typedef enum int {
    STATE_UNINIT = 0,
    STATE_INIT = 1,
    STATE_DONE = 2
  } state_e;

  state_e g_state = STATE_UNINIT;
  string deferred_q[$];

  class service_t;
    local static service_t inst;

    static function service_t get();
      if (inst == null) do_init();
      return inst;
    endfunction

    static function void set(service_t s);
      inst = s;
    endfunction
  endclass

  function automatic void do_init();
    service_t s;
    if (g_state != STATE_UNINIT) return;
    g_state = STATE_INIT;
    foreach (deferred_q[i]) begin
      // Process deferred registrations
    end
    deferred_q.delete();
    s = new();
    service_t::set(s);
    g_state = STATE_DONE;
  endfunction

  function void register_type(string name);
    if (g_state == STATE_UNINIT) begin
      deferred_q.push_back(name);
    end
  endfunction
endpackage

package pkg_b;
  import pkg_a::*;

  class component_c;
    function new(string name);
      service_t s;
      s = pkg_a::service_t::get();
    endfunction
  endclass

  component_c default_monitor = new("default_monitor");
endpackage

package pkg_c;
  import pkg_a::*;

  class registry_common;
    static bit m_initialized = deferred_init();

    static function bit deferred_init();
      if (pkg_a::g_state == STATE_UNINIT) begin
        pkg_a::register_type("test_class");
      end
      return 1;
    endfunction
  endclass
endpackage

module t;
  import pkg_a::*;
  import pkg_b::*;
  import pkg_c::*;

  initial begin
    service_t svc;
    svc = pkg_a::service_t::get();
    `checkd(pkg_a::deferred_q.size(), 0);
    `checkd(pkg_a::g_state, 32'd2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
