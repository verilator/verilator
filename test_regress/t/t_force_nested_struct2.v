// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2026 by Antmicro.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct packed {
  logic [31:0] value;
} Entry;

typedef struct packed {
  Entry [1:0][1:0] entries;
} DataBlock;

module sub;
  DataBlock data_block;
endmodule

module t;
  sub sub1 ();
  logic [31:0] forced_value;
  initial begin
    forced_value = 32'h00000001;
    force sub1.data_block.entries[0][0].value = forced_value[31:0];
    `checkh(sub1.data_block.entries[0][0].value[0], 1'b1);
    `checkh(sub1.data_block.entries[0][0].value, 32'h00000001);
    $finish;
  end
endmodule
