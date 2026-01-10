// DESCRIPTION: Verilator: Verilog Test module
//
// Copyright 2025 by Wilson Snyder. This program is free software; you can
// redistribute it and/or modify it under the terms of either the GNU
// Lesser General Public License Version 3 or the Perl Artistic License
// Version 2.0.
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

package pyhdl_if;

  typedef chandle PyObject;
  import "DPI-C" context function PyObject _pyhdl_if_PyTuple_GetItem(
    input PyObject p0,
    input longint unsigned p1
  );

  function PyObject PyTuple_GetItem(input PyObject p0, input longint unsigned p1);
    return _pyhdl_if_PyTuple_GetItem(p0, p1);
  endfunction

  class py_object;
    function new(PyObject obj);
    endfunction
  endclass

  class py_tuple;

    function py_object get_item(int idx);
      py_object ret = new(PyTuple_GetItem(null, longint'(idx)));
      return ret;
    endfunction

  endclass

endpackage

module t (
    input clk
);

  import pyhdl_if::*;

  initial begin
    py_tuple t0 = new;
    py_object o;
    o = t0.get_item(1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
