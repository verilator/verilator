// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2025 Antmicro
// SPDX-License-Identifier: CC0-1.0

module t;
  export "DPI-C" task cfunc_finish; // this is just so the task becomes AstCFunc, we don't really use the export
  task cfunc_finish;
    $finish;
  endtask

  initial begin
    fork
      cfunc_finish();
    join_none
    #1 $stop;
  end
endmodule
