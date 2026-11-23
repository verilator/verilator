// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// FIXME
// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);
// verilog_format: on

module t;
  typedef byte unsigned array_t [];
  typedef byte unsigned queue_t [$];

  string str_hello = "Hello world!";
  byte tmp_hello [12] = '{8'h48, 8'h65, 8'h6C, 8'h6C, 8'h6F, 8'h20, 8'h77, 8'h6F, 8'h72, 8'h6C, 8'h64, 8'h21};
  string str;
  array_t a;
  queue_t q;

  initial begin
    a = array_t'(str_hello);
    `checkd(a.size, 12);
    `checkd(a[0], 72);

    q = queue_t'(str_hello);
    `checkd(q.size, 12);
    `checkd(q[0], 72);

    str = string'(tmp_hello);
    `checks(str, "Hello world!");

    a = '{121, 101, 115};
    str = string'(a);
    `checks(str, "yes");

    q = '{121, 101, 115};
    str = string'(a);
    `checks(str, "yes");

    $finish;
  end
endmodule
/* FIXME see also t_string_byte.v
 */
