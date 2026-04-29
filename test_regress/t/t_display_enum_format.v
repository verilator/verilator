// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

module t (
    input string empty_no_opt
);
  typedef enum logic [1:0] {
    E0 = 0,
    E1 = 1,
    E2 = 2
  } my_e;

  typedef enum logic [63:0] {
    W64A = 64'h1,
    W64B = 64'h0000_0001_0000_0001
  } wide64_e;

  my_e e;
  wide64_e e64;
`define check(got, exp) do if ((got) != (exp)) begin \
      $write("%%Error: %s:%0d: got='%s' exp='%s'\n", `__FILE__, `__LINE__, got, exp); \
      $stop; \
    end while(0)

  initial begin
    string fmt;
    begin
      my_e it;
      string names_p;
      string names_s;
      string vals_d;
      names_p = "";
      names_s = "";
      vals_d = "";
      for (it = it.first; ; it = it.next) begin
        if (names_p != "") begin
          names_p = {names_p, ","};
          names_s = {names_s, ","};
          vals_d = {vals_d, ","};
        end
        names_p = {names_p, $sformatf("%p", it)};
        names_s = {names_s, $sformatf("%s", it)};
        vals_d = {vals_d, $sformatf("%0d", it)};
        if (it == it.last) break;
      end
      `check(names_p, "E0,E1,E2");
      `check(names_s, "E0,E1,E2");
      `check(vals_d, "0,1,2");
    end

    // Valid enum values print mnemonic for %p/%s.
    e = E0;
    `check($sformatf("%p", e), "E0");
    `check($sformatf("%s", e), "E0");

    e = E1;
    `check($sformatf("%p", e), "E1");
    `check($sformatf("%P", e), "E1");
    `check($sformatf("%0p", e), "E1");
    `check($sformatf("%s", e), "E1");
    `check($sformatf("%S", e), "E1");
    `check($sformatf("%d", e), "1");
    `check($sformatf("%0d", e), "1");
    `check($sformatf("%h", e), "1");
    `check($sformatf("%0h", e), "1");
    `check($sformatf("%b", e), "01");
    `check($sformatf("%0b", e), "1");
    `check($sformatf("%o", e), "1");
    `check($sformatf("%0o", e), "1");
    `check($sformatf("%x", e), "1");
    `check($sformatf("%0x", e), "1");

    e = E2;
    `check($sformatf("%p", e), "E2");
    `check($sformatf("%s", e), "E2");
    `check($sformatf("%s|%p", e, e), "E2|E2");
    `check($sformatf("%4p", e), "E2");
    `check($sformatf("%-4p", e), "E2");
    `check($sformatf("%d", e), "2");
    `check($sformatf("%h", e), "2");
    `check($sformatf("%b", e), "10");
    `check($sformatf("%0b", e), "10");
    `check($sformatf("%o", e), "2");
    `check($sformatf("%x", e), "2");
    `check($sformatf("%4d", e), "   2");
    `check($sformatf("%04d", e), "0002");
    `check($sformatf("%4h", e), "0002");
    `check($sformatf("%-4s", e), "E2  ");
    `check($sformatf("%4s", e), "  E2");
    // `%p`/`%s` in non-terminal positions with mixed formatters.
    `check($sformatf("%0d:%s:%0d", 9, e, 7), "9:E2:7");
    `check($sformatf("%s %h %p", e, 4'hA, e), "E2 a E2");
    `check($sformatf("pre %% %s post", e), "pre % E2 post");
    // Complex enum expressions (non-var-ref) in format args.
    `check($sformatf("%s", (1'b1 ? E2 : E0)), "E2");
    // 64-bit enums should preserve bits above 32 in both named and numeric cases.
    e64 = W64B;
    `check($sformatf("%p", e64), "W64B");
    `check($sformatf("%s", e64), "W64B");
    e64 = wide64_e'(64'h0000_0002_0000_0001);
    `check($sformatf("%p", e64), "8589934593");
    `check($sformatf("%s", e64), "8589934593");
    // Exercise display/write-family formatting path in addition to $sformatf checks.
    $display("display-valid:%s:%0d:%p", e, 7, e);
    $write("write-valid:%s:%0d:%p\n", e, 8, e);
    // Invalid enum values fall back to numeric formatting for %p/%s.
    e = my_e'(3);
    `check($sformatf("%p", e), "3");
    `check($sformatf("%P", e), "3");
    `check($sformatf("%0p", e), "'h3");
    `check($sformatf("%s", e), "3");
    `check($sformatf("%S", e), "3");
    `check($sformatf("%4p", e), "3");
    `check($sformatf("%4s", e), "   3");
    `check($sformatf("%d", e), "3");
    `check($sformatf("%0d", e), "3");
    `check($sformatf("%h", e), "3");
    `check($sformatf("%0h", e), "3");
    `check($sformatf("%b", e), "11");
    `check($sformatf("%0b", e), "11");
    `check($sformatf("%o", e), "3");
    `check($sformatf("%x", e), "3");
    // Non-terminal invalid-value fallback with mixed formatters.
    `check($sformatf("%0d:%p:%0d", 9, e, 7), "9:3:7");
    `check($sformatf("%s %h %p", e, 4'hA, e), "3 a 3");
    `check($sformatf("pre %% %s post", e), "pre % 3 post");
    `check($sformatf("%s|%p", e, e), "3|3");
    `check($sformatf("%s", (1'b1 ? my_e'(3) : E0)), "3");
    `check($sformatf("%p", (1'b0 ? E0 : my_e'(3))), "3");
    $display("display-invalid:%s:%0d:%p", e, 7, e);
    $write("write-invalid:%s:%0d:%p\n", e, 8, e);
    // Runtime-computed $sformatf formats should preserve enum mnemonic/fallback behavior.
    e = E2;
    fmt = {"%", "s", empty_no_opt};
    `check($sformatf(fmt, e), "E2");
    fmt = {"%", "p", empty_no_opt};
    `check($sformatf(fmt, e), "E2");
    fmt = {"%0d:%", "s", ":%0d", empty_no_opt};
    `check($sformatf(fmt, 9, e, 7), "9:E2:7");
    fmt = {"%", "s", " %h %", "p", empty_no_opt};
    `check($sformatf(fmt, e, 4'hA, e), "E2 a E2");
    e = my_e'(3);
    fmt = {"%", "s", empty_no_opt};
    `check($sformatf(fmt, e), "3");
    fmt = {"%", "p", empty_no_opt};
    `check($sformatf(fmt, e), "3");
    fmt = {"%0", "p", empty_no_opt};
    `check($sformatf(fmt, e), "'h3");
    fmt = {"%0d:%", "s", ":%0d", empty_no_opt};
    `check($sformatf(fmt, 9, e, 7), "9:3:7");
    fmt = {"%", "s", " %h %", "p", empty_no_opt};
    `check($sformatf(fmt, e, 4'hA, e), "3 a 3");
    fmt = {"%", "p", empty_no_opt};
    `check($sformatf(fmt, e64), "8589934593");

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
