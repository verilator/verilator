// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module rec #(parameter type T = bit[7:0]);
  parameter S = $bits(T);
  if ($bits(T) > 1) begin : Rec
    rec #(bit[$bits(T)/2-1:0]) child();
  end
endmodule

module t;
  rec #(bit[15:0]) r();
  initial begin
    `checkd(r.S, 16)
    `checkd(r.Rec.child.S, 8)
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
