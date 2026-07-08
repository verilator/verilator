// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
// verilog_format: on

module t;
  logic [31:0] b = 0;
  logic [31:0] d = 32'h1111_2222;
  wire [31:0] e;
  wire [7:0] f;
  wire [31:0] g;
  logic [4:0] idx = 0;
  sub s(b);
  sub8 s_sel(d[7:0]);
  sub8 s_const(8'h7c);
  subout s_out(e[idx+:8]);
  subout s_out_simple(f);
  subout s_out_slice(g[15:8]);

  initial begin
    #1;

    force s.c = 2;
    `checkh(s.c, 2);
    release s.c;
    `checkh(s.c, 0);

    `checkh(s_sel.c, 8'h22);
    force s_sel.c = 8'h33;
    `checkh(s_sel.c, 8'h33);
    release s_sel.c;
    `checkh(s_sel.c, 8'h22);

    `checkh(s_const.c, 8'h7c);
    force s_const.c = 8'ha5;
    `checkh(s_const.c, 8'ha5);
    release s_const.c;
    `checkh(s_const.c, 8'h7c);

    `checkh(s_out_simple.c, 8'h5a);
    force s_out_simple.c = 8'hc3;
    `checkh(s_out_simple.c, 8'hc3);
    release s_out_simple.c;
    `checkh(s_out_simple.c, 8'h5a);

    `checkh(f, 8'h5a);
    force f = 8'ha5;
    `checkh(f, 8'ha5);
    release f;
    `checkh(f, 8'h5a);

    `checkh(g[15:8], 8'h5a);
    force g[15:8] = 8'ha5;
    `checkh(g[15:8], 8'ha5);
    release g[15:8];
    `checkh(g[15:8], 8'h5a);

    force d = 32'h1234_5678;
    `checkh(d, 32'h1234_5678);
    release d;
    `checkh(d, 32'h1234_5678);

    idx = 5'd4;
    force idx = 5'd8;
    `checkh(idx, 5'd8);
    release idx;
    `checkh(idx, 5'd8);
    $finish;
  end

endmodule

module sub(input logic [31:0] c);
endmodule

module sub8(input logic [7:0] c);
endmodule

module subout(output logic [7:0] c);
  assign c = 8'h5a;
endmodule
