// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Parameterized classes of the same name in different scopes are different classes

package PkgBase;
  class Agent #(
      int W = 8
  );
    function int width();
      return W;
    endfunction
  endclass
endpackage

package PkgExt;
  class Agent #(
      int W = 8
  ) extends PkgBase::Agent #(W);
    function int twice();
      return 2 * width();
    endfunction
  endclass
endpackage

class OuterA;
  class Inner #(
      type T = int
  );
    T v;
    int a_only;
  endclass
  Inner #(byte) h;
endclass

class OuterB;
  class Inner #(
      type T = int
  );
    T v;
    int b_only;
  endclass
  Inner #(byte) h;
endclass

module t;
  initial begin
    automatic PkgExt::Agent #(16) ext = new;
    automatic PkgBase::Agent #(16) base = ext;
    automatic PkgBase::Agent #(16) base2 = new;
    automatic OuterA oa = new;
    automatic OuterB ob = new;
    `checkd(ext.twice(), 32);
    `checkd(base.width(), 16);
    `checkd(base2.width(), 16);
    oa.h = new;
    ob.h = new;
    oa.h.a_only = 1;
    ob.h.b_only = 2;
    `checkd(oa.h.a_only, 1);
    `checkd(ob.h.b_only, 2);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
