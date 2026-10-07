// DESCRIPTION: Verilator: %m in a module with several instances, whose code is combined
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

import "DPI-C" context function void dpic_scopes();

interface ifc;
  function automatic string name();
    return $sformatf("%m");
  endfunction
endinterface

module sub;
  initial $display("sub %m");
endmodule

module leaf;
  /*verilator no_inline_module*/
  sub u_sub ();
  task automatic show;
    $display("show %m");
  endtask
  initial begin
    $display("leaf %m");
    begin : named
      $display("named %m");
    end
    // Prints as is, though it looks like internal name encoding
    begin : x__PVT__y
      $display("pvt %m");
    end
    show();
  end
  // Calls into another instance keep its absolute scope name, 'u1' being a prefix of 'u10'
  final begin
    $display("final %m");
    t.u1.show();
    t.u10.show();
  end
endmodule

module t;
  leaf u1 ();
  leaf u10 ();
  ifc i1 ();
  ifc i2 ();
  virtual ifc v;
  initial begin
    // A virtual interface call runs one instance's copy of the function (#8770), which now
    // names the instance the handle points to
    v = i1;
    $display("vif %s", v.name());
    v = i2;
    $display("vif %s", v.name());
    dpic_scopes();
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
