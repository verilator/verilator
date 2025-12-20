// DESCRIPTION: Verilator: Regression test for scope/var lifetime issue
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0


package p;
  typedef chandle PyObject;

  class uvm_object;
  endclass

  class py_object;
    function new(PyObject o);
    endfunction
  endclass

  class pyhdl_uvm_object_rgy;
    static pyhdl_uvm_object_rgy m_inst;

    static function pyhdl_uvm_object_rgy inst();
      if (m_inst == null) m_inst = new;
      return m_inst;
    endfunction

    function PyObject wrap(uvm_object obj);
      if (obj == null) return null;
      return null;
    endfunction
  endclass

  class comp_proxy;
    virtual function PyObject get_config_object(string name, bit clone = 0);
      uvm_object obj;
      py_object py_obj;
      bit has = 0;

      if (has && obj != null) begin
        py_obj = new(pyhdl_uvm_object_rgy::inst().wrap(obj));
      end

      return null;
    endfunction
  endclass
endpackage

module t;
  import p::*;

  initial begin
    comp_proxy cp = new;
    void'(cp.get_config_object("x"));
    $finish;
  end
endmodule
