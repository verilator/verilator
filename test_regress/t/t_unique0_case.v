// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t;
  int x;
  int y;
  int z;
  initial begin
    y = 0;
    x = 0;
    z = 0;
    unique0 case(increment_x())
      1: begin
        y = 1;
      end
      default: begin
        z = 1;
      end
    endcase
    `checkh(x, 32'h1);
    `checkh(y, 32'h1);
    `checkh(z, 32'h0);
    $finish;
  end

  function automatic integer increment_x();
    x = x + 1;
    return x;
  endfunction
endmodule
