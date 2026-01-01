// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

typedef struct packed {
    logic sig1;
    logic sig2;
    logic not_forced;
} s1;

module t(clk);
    input clk;
    s1 s1inst;
    logic a = 1'b0;
    logic b;
    initial force s1inst.sig1 = a;
    always @(posedge clk) begin
        force s1inst.sig2 = 1'b1;
        force s1inst.sig1 = b;

        `checkh(s1inst.sig1, b);
        `checkh(s1inst.sig2, 1'b1);

        $finish;
    end
endmodule
