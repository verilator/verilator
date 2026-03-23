// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

module t;

  typedef struct {
    string path;
    int offset;
    int size;
  } uvm_hdl_path_slice;

  class ral_reg;
    function void add_hdl_path(uvm_hdl_path_slice slices[], string kind = "RTL");
      foreach (slices[i]) begin
        $display("Add %s", slices[i].path);
      end
    endfunction
  endclass

  class Cls;

    rand ral_reg m_counters[4];

    function new();
      foreach (this.m_counters[i]) begin
        this.m_counters[i] = new;
      end
    endfunction

    function void build();
      foreach (this.m_counters[i]) begin
        int J = i;
        // this.m_counters[J] = ral_reg_slave_B1_COUNTERS::type_id::create(
        //     $sformatf("COUNTERS[%0d]", J),, get_full_name());
        this.m_counters[J].add_hdl_path('{'{$sformatf("COUNTERS[%0d]", J), -1, -1}});
      end
    endfunction
  endclass

  initial begin
    Cls c;
    c = new;
    c.build;
    $finish;
  end

endmodule
