// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2008 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on

module t (
    input string empty_no_opt
);

  // Note $sscanf already tested elsewhere

  reg [3:0] n;
  reg [63:0] q;
  reg [16*8:1] wide;

  reg [8:1] ochar;
  reg [48*8:1] str;
  reg [48*8:1] str2;
  string str3;

  reg [39:0] instruction_str[1:0];

  real r;

  function string cvt2string(input int width, input int v);
    string fmt;
    $sformat(fmt, "%0d'h%%%0dh", width, (width - 1) / 4 + 1);
    $sformat(cvt2string, {"FMT=", fmt, empty_no_opt}, v);
    $display("Format '%s' -> '%s'", fmt, cvt2string);
  endfunction

  int mem[2] = '{1, 2};
  string s;

  initial begin
    n = 4'b1100;
    q = 64'h1234_5678_abcd_0123;
    wide = "hello-there12345";
    $sformat(str, "n=%b q=%d w=%s", n, q, wide);
    `checks(str, "n=1100 q= 1311768467750060323 w=hello-there12345");

    q = {q[62:0], 1'b1};
    $swrite(str2, "n=%b q=%d w=%s", n, q, wide);
    `checks(str2, "n=1100 q= 2623536935500120647 w=hello-there12345");

    str3 = $sformatf("n=%b q=%d w=%s", n, q, wide);
    `checks(str3, "n=1100 q= 2623536935500120647 w=hello-there12345");

    $swrite(str2, "e=%e", r);
    $swrite(str2, "e=%f", r);
    $swrite(str2, "e=%g", r);

    str3 = "hello";
    $swrite(str2, {str3, str3});
    `checks(str2, "hellohello");

    r = 0.01;
    $swrite(str2, "e=%e f=%f g=%g", r, r, r);
    `checks(str2, "e=1.000000e-02 f=0.010000 g=0.01");

    $swrite(str2, "mod=%m");
    `checks(str2, "mod=top.t");

    $swrite(str2, "lib=%l");
    `checks(str2, "lib=work.t");

    str3 = $sformatf("u=%u", {"a", "b", "c", "d"});  // Value selected so is printable
    `checks(str3, "u=dcba");

    str3 = $sformatf("v=%v", 4'b01xz);  // Value selected so is printable
`ifdef TEST_VERBOSE
    $display("chkv %s", str3);
`endif

    str3 = $sformatf("z=%z", {"a", "b", "c", "d"});  // Value selected so is printable
`ifdef TEST_VERBOSE
    $display("chkz %s", str3);
`endif

    $sformat(ochar, "%s", "c");
    `checks(ochar, "c");

    $swrite(str2, 4'd12);
    `checks(str2, "12");
    $swriteb(str2, 4'd12);
    `checks(str2, "1100");
    $swriteh(str2, 4'd12);
    `checks(str2, "c");
    $swriteo(str2, 4'd12);
    `checks(str2, "14");

    str3 = "foo";
    $sformat(str3, "%s", str3);  // $sformat twice so verilator does not
    $sformat(str3, "%s", str3);  // optimize the call to $sformat(str3, "%s", "foo")
    `checks(str3, "foo");

    $sformat(instruction_str[0], "%s", "Hello");
    $sformat(instruction_str[1], "%s", "World");
    `checks(instruction_str[0], "Hello");
    `checks(instruction_str[1], "World");

    s = cvt2string(`no_optimize(2), `no_optimize(2 * 16));
    `checks(s, "FMT=2'h20");

    s = cvt2string(`no_optimize(14), `no_optimize(14 * 16));
    `checks(s, "FMT=14'h00e0");

    s = "hello";
    s = $sformatf({"%x", "-const"}, s);
    `checks(s, "68656c6c6f-const");

    s = "hello";
    s = $sformatf({"%x", empty_no_opt}, s);
    `checks(s, "68656c6c6f");  // Simulators vary in output; hex required by V3Randomize
    // Also is more consistent with when have $sformat("%x", "string-as-verilog-number")

    s = $sformatf("%s", "constified");
    s = $sformatf("%s", s);
    s = $sformatf("%s", s);
    `checks(s, "constified");

    $display(mem);  // Implied %p

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
