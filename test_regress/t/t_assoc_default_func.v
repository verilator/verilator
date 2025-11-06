// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
  class param_comp #(
      type T = bit
  );
    static function int get_type();
      return 0;
    endfunction
  endclass

  class test;
    virtual function void check_phase();
      int m_param_comp_bit_expect_wrapper[string] = '{default: param_comp#(bit)::get_type()};
    endfunction
  endclass
endmodule
