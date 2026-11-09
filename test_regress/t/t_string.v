// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2014 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=\"%s\" exp=\"%s\"\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input clk
);

  integer cyc = 0;

  reg [1*8:1] vstr1;
  reg [2*8:1] vstr2;
  reg [6*8:1] vstr6;

  reg [4*8:1] vstr;
  const string s = "a";  // Check static assignment
  string s2;
  string s3;
  reg eq;

  byte unpack1[0:4];

  // Operators == != < <= > >=  {a,b}  {a{b}}  a[b]
  // a.len, a.putc, a.getc, a.toupper, a.tolower, a.compare, a.icompare, a.substr
  // a.atoi, a.atohex, a.atooct, a.atobin, a.atoreal,
  // a.itoa, a.hextoa, a.octoa, a.bintoa, a.realtoa

  initial begin
    $sformat(vstr1, "%s", s);
    `checks(vstr1, "a");

    $sformat(vstr2, "=%s", s);
    `checks(vstr2, "=a");

    $sformat(vstr6, "--a=%s", s);
    `checks(vstr6, "--a=a");

    $sformat(vstr, "s=%s", s);
    `checks(vstr, "s=a");
    `checks(string'(vstr), "s=a");
    `checks(s, "a");
    `checks({s, s, s}, "aaa");
    `checks({4{s}}, "aaaa");
    // Constification
    `checkh(s == "a", 1'b1);
    `checkh(s == "b", 1'b0);
    `checkh(s != "a", 1'b0);
    `checkh(s != "b", 1'b1);
    `checkh(s > " ", 1'b1);
    `checkh(s > "a", 1'b0);
    `checkh(s >= "a", 1'b1);
    `checkh(s >= "b", 1'b0);
    `checkh(s < "a", 1'b0);
    `checkh(s < "b", 1'b1);
    `checkh(s <= " ", 1'b0);
    `checkh(s <= "a", 1'b1);

`ifndef VCS
`ifndef VERILATOR
`ifndef NC
    // IEEE 1800-2023 5.9 assignment to byte array
    unpack1 = "five";
    `checkh(unpack1[0], "f");
    `checkh(unpack1[1], "i");
    `checkh(unpack1[2], "v");
    `checkh(unpack1[3], "e");
    `checkh(unpack1[4], 8'h0);
`endif
`endif
`endif
  end

  // String as a condition is true when non-empty
  initial begin
    // Values known at compile time
    string full;
    string empty;
    int n;
    full = "abc";
    empty = "";
    if (full) n += 1;
    if (empty) n += 2;
    `checkd(n, 1);
  end

  typedef string str_t;
  class StrCond;
    str_t str;
    function int count();
      int n = 0;
      if (str) n += 1;
      n += str ? 2 : 0;
      for (str_t rest = str; rest; rest = rest.substr(1, rest.len() - 1)) n += 4;
      return n;
    endfunction
  endclass

  always @(posedge clk) begin
    // Values known only at runtime
    StrCond c;
    c = new;
    if (cyc[0]) c.str = "ab";
    `checkd(c.count(), cyc[0] ? 11 : 0);
  end

  // Concatenations with formatted strings
  always @(posedge clk) begin
    string fmt;
    if (cyc == 5) begin
      // Empty string
      `checks({"", $sformatf("%0d", cyc)}, "5");
      `checks({$sformatf("%0d", cyc), ""}, "5");
      `checks({"", {" ", $sformatf("%0d", cyc)}}, " 5");
      // Constant text in the format, where '%' is not a format code
      `checks({"%d", $sformatf("%0d", cyc)}, "%d5");
      `checks({$sformatf("%0d", cyc), "%%"}, "5%%");
      // Two formats with their arguments
      `checks({$sformatf("%0d", cyc), $sformatf("-%0h", cyc + 10)}, "5-f");
      // Format of a format
      `checks($sformatf("<%s|%0d>", $sformatf("%0d-%0h", cyc, cyc + 10), cyc), "<5-f|5>");
      `checks($sformatf("[%3s]", $sformatf("%0d", cyc)), "[  5]");
      // Format of a concatenation
      fmt = cyc[0] ? "y" : "n";
      `checks($sformatf("<%s>", {"%", $sformatf("%0d", cyc), fmt}), "<%5y>");
      // Format of only a string
      `checks({$sformatf("%s", fmt), "!"}, "y!");
      $sformat(vstr, "%s", fmt);
      `checks(vstr, "y");
      begin
        string copy;
        $sformat(copy, "%s", fmt);
        `checks(copy, "y");
      end
      // Format only known at runtime
      fmt = cyc[0] ? "<%0d>" : "[%0d]";
      `checks({"x", $sformatf(fmt, cyc)}, "x<5>");
    end
  end

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      // Setup
      s2 = "c0";
    end
    else if (cyc == 1) begin
      $sformat(vstr, "s2%s", s2);
      `checks(vstr, "s2c0");
    end
    else if (cyc == 2) begin
      s3 = s2;
      $sformat(vstr, "s2%s", s3);
      `checks(vstr, "s2c0");
    end
    else if (cyc == 3) begin
      s2 = "a";
      s3 = "b";
    end
    else if (cyc == 4) begin
      `checks({s2, s3}, "ab");
      `checks({3{s3}}, "bbb");
      `checkh(s == "a", 1'b1);
      `checkh(s == "b", 1'b0);
      `checkh(s != "a", 1'b0);
      `checkh(s != "b", 1'b1);
      `checkh(s > " ", 1'b1);
      `checkh(s > "a", 1'b0);
      `checkh(s >= "a", 1'b1);
      `checkh(s >= "b", 1'b0);
      `checkh(s < "a", 1'b0);
      `checkh(s < "b", 1'b1);
      `checkh(s <= " ", 1'b0);
      `checkh(s <= "a", 1'b1);
    end
    // String character references
    else if (cyc == 10) begin
      s2 = "astring";
    end
    else if (cyc == 11) begin
      `checks(s2, "astring");
      `checkh(s2.len(), 7);
      `checkh(s2[1], "s");
      s2[0] = "0";
      s2[3] = "3";
      `checks(s2, "0st3ing");
    end
    //
    else if (cyc == 99) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end

endmodule
