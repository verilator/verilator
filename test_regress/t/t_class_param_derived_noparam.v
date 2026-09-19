// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

// Base class with type parameter
class base_type #(type T = int);
  function int width();
    T t;
    return $bits(t);
  endfunction
endclass

// No type parameters of its own, inherits the base's default
class default_type extends base_type;
endclass

// No type parameters of its own, overrides the base's parameter
class byte_type extends base_type #(byte);
endclass

// No type parameters of its own, empty parameter list on the extends clause
class paren_type extends base_type#();
endclass

// Base class with value parameter
class base_val #(int N = 32);
  function int val();
    return N;
  endfunction
endclass

// No parameters of its own, inherits the base's default
class default_val extends base_val;
endclass

// No parameters of its own, overrides the base's parameter
class eight_val extends base_val #(8);
endclass

// No parameters of its own, empty parameter list on the extends clause
class paren_val extends base_val#();
endclass

// Base class with no parameters at all
class base_none;
  function int width();
    return 1;
  endfunction
endclass

class paren_none extends base_none#();
endclass

class noparen_none extends base_none;
endclass

module t;

  // Referenced with an empty parameter list, and without one
  default_type#() dp = new;
  default_type dn = new;
  byte_type#() bp = new;
  byte_type bn = new;
  paren_type#() tp = new;
  paren_type tn = new;
  default_val#() vp = new;
  default_val vn = new;
  eight_val#() ep = new;
  eight_val en = new;
  paren_val#() qp = new;
  paren_val qn = new;
  paren_none#() pp = new;
  paren_none pn = new;
  noparen_none#() np = new;
  noparen_none nn = new;

  initial begin
    `checkh(dp.width(), 32);
    `checkh(dn.width(), 32);
    `checkh(bp.width(), 8);
    `checkh(bn.width(), 8);
    `checkh(tp.width(), 32);
    `checkh(tn.width(), 32);
    `checkh(vp.val(), 32);
    `checkh(vn.val(), 32);
    `checkh(ep.val(), 8);
    `checkh(en.val(), 8);
    `checkh(qp.val(), 32);
    `checkh(qn.val(), 32);
    `checkh(pp.width(), 1);
    `checkh(pn.width(), 1);
    `checkh(np.width(), 1);
    `checkh(nn.width(), 1);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
