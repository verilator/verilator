// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t (
    input no_opt
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
  typedef enum logic [95:0] {
    W96A = 96'h1,
    W96B = 96'hA_0000_0000_0000_0001
  } wide96_e;
  typedef logic signed [4095:0] uvm_bitstream_t;

  // IEEE 1800-2023 21.2.1.6 permits implementation-specific %0p output.
`ifdef QUESTA
  localparam string COMPACT_NUM_PREFIX = "";
`else
  localparam string COMPACT_NUM_PREFIX = "'h";
`endif

  my_e e;
  wide64_e e64;
  wide96_e e96;
  logic [63:0] n64;
  uvm_bitstream_t bitstream_value;

  initial begin
    string fmt;
    string formatted;
    string empty_no_opt;
    // Keep formats nonconstant using an input supported by the generated testbench.
    empty_no_opt = (no_opt === 1'b1) ? "unexpected" : "";
    begin
      my_e it;
      string names_p;
      string names_s;
      string vals_d;
      names_p = "";
      names_s = "";
      vals_d = "";
      for (it = it.first;; it = it.next) begin
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
      `checks(names_p, "E0,E1,E2");
      `checks(names_s, "E0,E1,E2");
      `checks(vals_d, "0,1,2");
    end

    // Valid enum values print mnemonic for %p/%s.
    e = E0;
    `checks($sformatf("%p", e), "E0");
    `checks($sformatf("%s", e), "E0");

    e = E1;
    `checks($sformatf("%p", e), "E1");
    `checks($sformatf("%P", e), "E1");
    `checks($sformatf("%0p", e), "E1");
    `checks($sformatf("%s", e), "E1");
    `checks($sformatf("%S", e), "E1");
    `checks($sformatf("%d", e), "1");
    `checks($sformatf("%0d", e), "1");
    `checks($sformatf("%h", e), "1");
    `checks($sformatf("%0h", e), "1");
    `checks($sformatf("%b", e), "01");
    `checks($sformatf("%0b", e), "1");
    `checks($sformatf("%o", e), "1");
    `checks($sformatf("%0o", e), "1");
    `checks($sformatf("%x", e), "1");
    `checks($sformatf("%0x", e), "1");

    e = E2;
    `checks($sformatf("%p", e), "E2");
    `checks($sformatf("%s", e), "E2");
    `checks($sformatf("%s|%p", e, e), "E2|E2");
    // IEEE 1800-2023 21.2.1.6 specifies %p/%0p, not nonzero %p field widths.
    formatted = $sformatf("%4p/%-4p", e, e);
`ifdef QUESTA
    `checks(formatted, "00E2/E2  ");
`else
    `checks(formatted, "E2/E2");
`endif
    `checks($sformatf("%d", e), "2");
    `checks($sformatf("%h", e), "2");
    `checks($sformatf("%b", e), "10");
    `checks($sformatf("%0b", e), "10");
    `checks($sformatf("%o", e), "2");
    `checks($sformatf("%x", e), "2");
    `checks($sformatf("%4d", e), "   2");
    formatted = $sformatf("%04d", e);
`ifdef QUESTA
    `checks(formatted, "   2");
`else
    `checks(formatted, "0002");
`endif
    `checks($sformatf("%4h", e), "0002");
    `checks($sformatf("%-4s", e), "E2  ");
    `checks($sformatf("%4s", e), "  E2");
    // `%p`/`%s` in non-terminal positions with mixed formatters.
    `checks($sformatf("%0d:%s:%0d", 9, e, 7), "9:E2:7");
    `checks($sformatf("%s %h %p", e, 4'hA, e), "E2 a E2");
    `checks($sformatf("pre %% %s post", e), "pre % E2 post");
    // Complex enum expressions (non-var-ref) in format args.
    `checks($sformatf("%s", (1'b1 ? E2 : E0)), "E2");
    // 64-bit enums should preserve bits above 32 in both named and numeric cases.
    e64 = W64B;
    `checks($sformatf("%p", e64), "W64B");
    `checks($sformatf("%s", e64), "W64B");
    e64 = wide64_e'(64'h0000_0002_0000_0001);
    `checks($sformatf("%p", e64), "8589934593");
    `checks($sformatf("%s", e64), "8589934593");
    n64 = 64'h0000_0000_0000_0001;
    formatted = $sformatf("%0p", n64);
    `checks(formatted, {COMPACT_NUM_PREFIX, "1"});
    // Wide enums use names for %p/%s without changing explicit numeric formats.
    e96 = W96B;  // 10 * 2**64 + 1
    if (empty_no_opt != "") e96 = W96A;  // Defeat constant folding
    formatted = $sformatf("%p", e96);
    `checks(formatted, "W96B");
    formatted = $sformatf("%s", e96);
    `checks(formatted, "W96B");
    formatted = $sformatf("%0p", e96);
    `checks(formatted, "W96B");
    `checks($sformatf("%0d", e96), "184467440737095516161");
    `checks($sformatf("%0h", e96), "a0000000000000001");
    // Exercise display/write-family formatting path in addition to $sformatf checks.
    $display("display-valid:%s:%0d:%p", e, 7, e);
    $write("write-valid:%s:%0d:%p\n", e, 8, e);
    // Invalid enum values fall back to numeric formatting for %p/%s.
    e = my_e'(3);
    `checks($sformatf("%p", e), "3");
    `checks($sformatf("%P", e), "3");
    formatted = $sformatf("%0p", e);
    `checks(formatted, {COMPACT_NUM_PREFIX, "3"});
    `checks($sformatf("%s", e), "3");
    `checks($sformatf("%S", e), "3");
    formatted = $sformatf("%4p", e);
`ifdef QUESTA
    `checks(formatted, "0003");
`else
    `checks(formatted, "3");
`endif
    `checks($sformatf("%4s", e), "   3");
    `checks($sformatf("%d", e), "3");
    `checks($sformatf("%0d", e), "3");
    `checks($sformatf("%h", e), "3");
    `checks($sformatf("%0h", e), "3");
    `checks($sformatf("%b", e), "11");
    `checks($sformatf("%0b", e), "11");
    `checks($sformatf("%o", e), "3");
    `checks($sformatf("%x", e), "3");
    // Non-terminal invalid-value fallback with mixed formatters.
    `checks($sformatf("%0d:%p:%0d", 9, e, 7), "9:3:7");
    `checks($sformatf("%s %h %p", e, 4'hA, e), "3 a 3");
    `checks($sformatf("pre %% %s post", e), "pre % 3 post");
    `checks($sformatf("%s|%p", e, e), "3|3");
    `checks($sformatf("%s", (1'b1 ? my_e'(3) : E0)), "3");
    `checks($sformatf("%p", (1'b0 ? E0 : my_e'(3))), "3");
    $display("display-invalid:%s:%0d:%p", e, 7, e);
    $write("write-invalid:%s:%0d:%p\n", e, 8, e);
    // Runtime-computed $sformatf formats should preserve enum mnemonic/fallback behavior.
    e = E2;
    fmt = {"%", "s", empty_no_opt};
    `checks($sformatf(fmt, e), "E2");
    fmt = {"%", "p", empty_no_opt};
    `checks($sformatf(fmt, e), "E2");
    fmt = {"%0h", empty_no_opt};
    formatted = $sformatf(fmt, e);
    `checks(formatted, "2");
    fmt = {"%0d:%", "s", ":%0d", empty_no_opt};
    `checks($sformatf(fmt, 9, e, 7), "9:E2:7");
    fmt = {"%", "s", " %h %", "p", empty_no_opt};
    `checks($sformatf(fmt, e, 4'hA, e), "E2 a E2");
    e = my_e'(3);
    fmt = {"%0b", empty_no_opt};
    formatted = $sformatf(fmt, e);
    `checks(formatted, "11");
    fmt = {"%", "s", empty_no_opt};
    `checks($sformatf(fmt, e), "3");
    fmt = {"%", "p", empty_no_opt};
    `checks($sformatf(fmt, e), "3");
    fmt = {"%0", "p", empty_no_opt};
    formatted = $sformatf(fmt, e);
    `checks(formatted, {COMPACT_NUM_PREFIX, "3"});
    fmt = {"%0d:%", "s", ":%0d", empty_no_opt};
    `checks($sformatf(fmt, 9, e, 7), "9:3:7");
    fmt = {"%", "s", " %h %", "p", empty_no_opt};
    `checks($sformatf(fmt, e, 4'hA, e), "3 a 3");
    fmt = {"%", "p", empty_no_opt};
    `checks($sformatf(fmt, e64), "8589934593");
    // Runtime formats must also preserve the wide enum's name.
    fmt = {"%", "p", empty_no_opt};
    formatted = $sformatf(fmt, e96);
    `checks(formatted, "W96B");
    fmt = {"%0d", empty_no_opt};
    `checks($sformatf(fmt, e96), "184467440737095516161");
    bitstream_value = 30;
    `checks($sformatf("%0s%0t", "", bitstream_value), "30");
    bitstream_value = '0;
    bitstream_value[32] = 1'b1;
    `checks($sformatf("%0s%0t", "", bitstream_value), "4294967296");
    bitstream_value = '0;
    bitstream_value[63:0] = 64'h0000_0001_0000_0001;
    `checks($sformatf("%0s%0t", "", bitstream_value), "4294967297");
    bitstream_value[7:0] = "A";
    // verilator lint_off WIDTHTRUNC
    `checks($sformatf("%c", bitstream_value), "A");
    // verilator lint_on WIDTHTRUNC

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
