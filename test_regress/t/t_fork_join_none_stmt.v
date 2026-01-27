// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bit stmt2 = '0;
  bit proc1 = '0;

  initial begin
    $display("Statement 1");
    fork
      begin
        // The join_none implies that here there's effectively a: #0;
        $display("Process 1");
        proc1 = '1;
        `checkh(stmt2, 1'b1);
      end
    join_none
    $display("Statement 2");
    stmt2 = '1;
    `checkh(proc1, 1'b0);

    #1;
    `checkh(proc1, 1'b1);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
