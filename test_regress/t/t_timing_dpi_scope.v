// DESCRIPTION: Verilator: Preserve DPI scope across a suspended export
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module child #(
    parameter bit CALL = 0
);
  import "DPI-C" context task ctask();
  import "DPI-C" context function void perturb();
  export "DPI-C" task exported;

  int unsigned export_count = 0;

  task automatic exported();
    #2;
    export_count++;
  endtask

  initial begin
    if (CALL) ctask();
    else begin
      #1;
      perturb();
    end
  end
endmodule

module t;
  child #(.CALL(1)) a ();
  child #(.CALL(0)) b ();

  initial begin
    #5;
    `checkd(a.export_count, 2);
    `checkd(b.export_count, 0);
    $finish;
  end
endmodule
