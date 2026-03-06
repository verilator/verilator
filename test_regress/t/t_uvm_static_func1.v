// DESCRIPTION: Verilator: Static function call on class with parameterized extends
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

package uvm_pkg;

  class uvm_tlm_extension #(
    type T = int
  );
    static function int ID();
      return 42;
    endfunction
  endclass
endpackage

import uvm_pkg::*;

module t;
  class ext1 extends uvm_tlm_extension #(ext1);
  endclass
  class ext2 extends uvm_tlm_extension;
  endclass

  class test;
    task run_phase();
      int i, j;
      i = ext2::ID();
      `checkd(i, 42);
      j = ext1::ID();
      `checkd(j, 42);
    endtask
  endclass

  initial begin
    test tst;
    tst = new;
    tst.run_phase;
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
