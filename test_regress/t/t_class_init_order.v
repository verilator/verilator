// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  class uvm_coreservice;
    static uvm_coreservice inst;

    function new(string name);
    endfunction

    static function uvm_coreservice get();
      if (inst == null) begin
        inst = new("cs-base");
      end
      return inst;
    endfunction

    virtual function string get_factory();
      return "factory";
    endfunction
  endclass

  class uvm_test;
    string m_name;
    string s0 = {m_name, "0"};  // Before new(); this must get "0" not "name0"
    function new(string name);
      m_name = name;
    endfunction
  endclass

  class test extends uvm_test;

    string s1 = {s0, "1"};
    string s2 = {s1, "2"};

    uvm_coreservice cs = uvm_coreservice::get();
    // Below assumes that the above 'cs' executes first.
    // Most simulators require this ordering, but some allow arbitrary order
    // This would require dataflow analysis, so for now Verilator requires user ordering
    string factory = cs.get_factory();

    function new(string name);
      super.new(name);
    endfunction
  endclass
  initial begin
    test t;
    string s;

    t = new("test");
    `checks(t.s0, "0");
    `checks(t.s1, "01");
    `checks(t.s2, "012");
    s = t.factory;
    `checks(s, "factory");

    $finish;
  end
endmodule
