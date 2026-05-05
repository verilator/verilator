// DESCRIPTION: Verilator: Verilog Test module
//
// Regression test for a parameterized-class typedef-chain bug.
//
// A parameterized class M re-typedefs a nested type from another
// parameterized class D (M::beat_t = M::driver_t::beat_t). When M and D
// are each instantiated with two distinct parameter values, the type of
// an M::beat_t local must resolve to the matching specialization of beat
// for the enclosing M instantiation. Previously the second sibling clone
// stomped the typedefp binding on the first sibling's REFDTYPE, producing
// a spurious "Function Argument expects ... beat__I5, got ... beat__I6"
// error.
//
// Reduced from axi_test::axi_rand_master usage in pulp-platform/axi
// (tb_axi_xbar with NumMasters>1 or NumSlaves>1).
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

package pkg;

  class beat #(parameter int IW = 8);
    logic [IW-1:0] id;
  endclass

  class driver #(parameter int IW = 8);
    typedef beat #(.IW(IW)) beat_t;
    task send(input beat_t b);
    endtask
  endclass

  class master #(parameter int IW = 8);
    typedef driver #(.IW(IW)) driver_t;
    typedef driver_t::beat_t  beat_t;

    driver_t drv;
    function new(driver_t d); drv = d; endfunction

    task run();
      automatic beat_t b = new;
      drv.send(b);
    endtask
  endclass

endpackage

module t;
  pkg::master #(.IW(5)) ma;
  pkg::master #(.IW(6)) mb;
  pkg::driver #(.IW(5)) da;
  pkg::driver #(.IW(6)) db;
  initial begin
    da = new; ma = new(da); ma.run();
    db = new; mb = new(db); mb.run();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
