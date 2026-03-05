// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Issue #7195
module t;

  class uvm_reg;
  endclass

  class reg_slave_DATA extends uvm_reg;
  endclass

  class reg_slave_TABLES extends uvm_reg;
    function uvm_reg create(string name = "");
      reg_slave_TABLES tmp;
      tmp = new;
      return tmp;
    endfunction
  endclass

  class reg_block_slave;
    reg_slave_DATA DATA;
    rand reg_slave_TABLES TABLES[4];

    virtual function void build();
      foreach (TABLES[i])
        TABLES[i] = new;
      this.configure(TABLES);  // Issue was here
    endfunction

    function void configure(uvm_reg reg_a[]);
      foreach (reg_a[i])
        $display("%p", reg_a[i]);
    endfunction
  endclass

  initial begin
    reg_block_slave c;
    c = new;
    c.build;
    $finish;
  end

endmodule
