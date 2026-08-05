// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 BRDR LIFE
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.5.14.2 lets 'disable soft' name a constraint_primary, which
// permits a select.  An array is one solver variable whose elements are not
// separately named, so a single element cannot be singled out; that has to be
// reported rather than aborting the run.  Naming the whole array works.

class C;
  rand bit [7:0] a[2];
  constraint c_soft { soft a[0] == 8'd5; }
  constraint c_disable { disable soft a[0]; }
endclass

module t;
  initial begin
    C o;
    o = new;
    void'(o.randomize());
    $stop;
  end
endmodule
