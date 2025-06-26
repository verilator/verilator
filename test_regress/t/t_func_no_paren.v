// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

package pkg;
   class tb_cpu_seq_item;
      virtual function void uvm_report_error(string message);
         $display("%s", message);
      endfunction
      virtual function string get_type_name();
         return "GTN";
      endfunction
      virtual function bit do_compare( tb_cpu_seq_item rhs, int comparer);
         uvm_report_error($sformatf("this is of type %s, rhs is of type %s", this.get_type_name(), rhs.get_type_name()));
         uvm_report_error($sformatf("this is of type %s, rhs is of type %s", this.get_type_name, rhs.get_type_name));
      endfunction
   endclass
endpackage

module t;
endmodule
