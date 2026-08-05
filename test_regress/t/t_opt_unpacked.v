// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// This test purpose is to make sure we do not drop if conditional
// expression when trying to optimise bit operations.
module t;
  class Cls;
  endclass;

  class subCls;
    bit val = 1'b1;
    Cls c;

    function void check_valid();
      // "c == null" shall be preserved
      if (val && c == null) begin
        $stop();
      end
    endfunction
  endclass;

  subCls sc;

  initial begin
    sc = new;
    sc.c = new;
    sc.check_valid();
    $finish;
  end
endmodule
