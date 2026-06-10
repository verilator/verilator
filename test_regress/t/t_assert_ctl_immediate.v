// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2024 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t (
    input clk
);

  module_with_assert module_with_assert (clk);
  module_with_assertctl module_with_assertctl (clk);
  module_with_method_ctl module_with_method_ctl ();

  always @(posedge clk) begin
    assert (0);
  end

  always @(negedge clk) begin
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module module_with_assert (
    input clk
);
  always @(posedge clk) assert (0);
endmodule

module module_with_assertctl (
    input clk
);
  function void assert_off;
    begin
      $assertoff;
    end
  endfunction
  function void assert_on;
    begin
      $asserton;
    end
  endfunction
  function void f_assert;
    begin
      assert (0);
    end
  endfunction

  initial begin
    assert_on();
    assert (0);
    assert_off();
    assert_off();
    assert (0);
    assert_on();
    assert_on();
    assert (0);

    f_assert();
    f_assert();
    assert_off();
    f_assert();
    f_assert();
  end
endmodule

// Assertion control invoked from class methods and interface functions, in a
// single sub-module with a single initial block so the golden output order is
// stable across --fno-inline (otherwise parallel sub-module initials are
// interleaved differently by the inliner).
//
// Covers:
//   - class task $assertoff / $asserton
//   - class static method $assertcontrol(Off=4 / On=3), IEEE 1800-2023 Table 20-5
//   - $assertkill from a class method
//   - assert that lives inside a class method (obeys context-global gating)
//   - interface function $assertoff / $asserton
//   - assert inside an interface function
//   - virtual interface dispatch to an assertion-control function
//   - interface class (AstClass with isInterfaceClass) via a concrete impl

interface AssertCtlIf;
  function void suppress();
    $assertoff;
  endfunction
  function void enable();
    $asserton;
  endfunction
  function void check_positive(int v);
    assert (v > 0);
  endfunction
endinterface

// verilog_format: off  (verible-verilog-format mangles `pure virtual function`)
interface class IAssertCtl;
  pure virtual function void suppress();
  pure virtual function void enable();
endclass
// verilog_format: on

class IAssertCtlImpl implements IAssertCtl;
  virtual function void suppress();
    $assertoff;
  endfunction
  virtual function void enable();
    $asserton;
  endfunction
endclass

module module_with_method_ctl;
  class Ctl;
    virtual AssertCtlIf vif;
    static function void off_all();
      $assertcontrol(4);
    endfunction
    static function void on_all();
      $asserton;
    endfunction
    function void kill_all();
      $assertkill;
    endfunction
    function void check_positive(int v);
      assert (v > 0);
    endfunction
    function void vif_suppress();
      vif.suppress();
    endfunction
    function void vif_enable();
      vif.enable();
    endfunction
  endclass

  Ctl c;
  AssertCtlIf iface ();
  IAssertCtlImpl impl;

  initial begin
    c = new;
    impl = new;

    // --- class method coverage ---
    Ctl::off_all();
    assert (0);  // gated via class static -> no fire
    Ctl::on_all();
    assert (0);  // fires
    Ctl::off_all();
    c.check_positive(-1);  // assert inside class method, gated -> no fire
    Ctl::on_all();
    c.check_positive(-2);  // assert inside class method, fires

    // --- interface function coverage ---
    iface.suppress();
    assert (0);  // gated via iface fn -> no fire
    iface.enable();
    assert (0);  // fires
    iface.suppress();
    iface.check_positive(-1);  // assert inside iface fn, gated -> no fire
    iface.enable();
    iface.check_positive(-2);  // assert inside iface fn, fires

    // --- virtual interface dispatch coverage ---
    c.vif = iface;
    c.vif_suppress();
    assert (0);  // gated via virtual interface dispatch -> no fire
    c.vif_enable();
    assert (0);  // fires

    // --- interface class via concrete impl ---
    impl.suppress();
    assert (0);  // gated via interface-class impl -> no fire
    impl.enable();
    assert (0);  // fires

    // --- $assertkill (last: terminal per IEEE 1800-2023 Table 20-5) ---
    c.kill_all();
    assert (0);  // killed -> no fire
  end
endmodule
