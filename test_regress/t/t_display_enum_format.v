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
        names_p = {names_p, $sformatf("%p/%p", it, it)};
        names_s = {names_s, $sformatf("%s/%s", it, it)};
        vals_d = {vals_d, $sformatf("%0d/%0d", it, it)};
        if (it == it.last) break;
      end
      `checks(names_p, "E0/E0,E1/E1,E2/E2");
      `checks(names_s, "E0/E0,E1/E1,E2/E2");
      `checks(vals_d, "0/0,1/1,2/2");
    end

    // Valid enum values print mnemonic for %p/%s.
    e = E0;
    formatted = $sformatf("%p/%p", e, e);
    `checks(formatted, "E0/E0");
    formatted = $sformatf("%s/%s", e, e);
    `checks(formatted, "E0/E0");

    e = E1;
    formatted = $sformatf("%p/%p", e, e);
    `checks(formatted, "E1/E1");
    formatted = $sformatf("%P/%P", e, e);
    `checks(formatted, "E1/E1");
    formatted = $sformatf("%0p/%0p", e, e);
    `checks(formatted, "E1/E1");
    formatted = $sformatf("%s/%s", e, e);
    `checks(formatted, "E1/E1");
    formatted = $sformatf("%S/%S", e, e);
    `checks(formatted, "E1/E1");
    formatted = $sformatf("%d/%d", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%0d/%0d", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%h/%h", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%0h/%0h", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%b/%b", e, e);
    `checks(formatted, "01/01");
    formatted = $sformatf("%0b/%0b", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%o/%o", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%0o/%0o", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%x/%x", e, e);
    `checks(formatted, "1/1");
    formatted = $sformatf("%0x/%0x", e, e);
    `checks(formatted, "1/1");

    e = E2;
    formatted = $sformatf("%p/%p", e, e);
    `checks(formatted, "E2/E2");
    formatted = $sformatf("%s/%s", e, e);
    `checks(formatted, "E2/E2");
    `checks($sformatf("%s|%p", e, e), "E2|E2");
    // IEEE 1800-2023 21.2.1.6 specifies %p/%0p, not nonzero %p field widths.
    formatted = $sformatf("%4p/%-4p", e, e);
`ifdef QUESTA
    `checks(formatted, "00E2/E2  ");
`else
    `checks(formatted, "E2/E2");
`endif
    formatted = $sformatf("%d/%d", e, e);
    `checks(formatted, "2/2");
    formatted = $sformatf("%h/%h", e, e);
    `checks(formatted, "2/2");
    formatted = $sformatf("%b/%b", e, e);
    `checks(formatted, "10/10");
    formatted = $sformatf("%0b/%0b", e, e);
    `checks(formatted, "10/10");
    formatted = $sformatf("%o/%o", e, e);
    `checks(formatted, "2/2");
    formatted = $sformatf("%x/%x", e, e);
    `checks(formatted, "2/2");
    formatted = $sformatf("%4d/%4d", e, e);
    `checks(formatted, "   2/   2");
    formatted = $sformatf("%04d/%04d", e, e);
`ifdef QUESTA
    `checks(formatted, "   2/   2");
`else
    `checks(formatted, "0002/0002");
`endif
    formatted = $sformatf("%4h/%4h", e, e);
    `checks(formatted, "0002/0002");
    formatted = $sformatf("%-4s/%-4s", e, e);
    `checks(formatted, "E2  /E2  ");
    formatted = $sformatf("%4s/%4s", e, e);
    `checks(formatted, "  E2/  E2");
    // `%p`/`%s` in non-terminal positions with mixed formatters.
    `checks($sformatf("%0d:%s:%0d", 9, e, 7), "9:E2:7");
    `checks($sformatf("%s %h %p", e, 4'hA, e), "E2 a E2");
    formatted = $sformatf("pre %% %s/%s post", e, e);
    `checks(formatted, "pre % E2/E2 post");
    // Complex enum expressions (non-var-ref) in format args.
    formatted = $sformatf("%s/%s", (1'b1 ? E2 : E0), (1'b1 ? E2 : E0));
    `checks(formatted, "E2/E2");
    // 64-bit enums should preserve bits above 32 in both named and numeric cases.
    e64 = W64B;
    formatted = $sformatf("%p/%p", e64, e64);
    `checks(formatted, "W64B/W64B");
    formatted = $sformatf("%s/%s", e64, e64);
    `checks(formatted, "W64B/W64B");
    e64 = wide64_e'(64'h0000_0002_0000_0001);
    formatted = $sformatf("%p/%p", e64, e64);
    `checks(formatted, "8589934593/8589934593");
    formatted = $sformatf("%s/%s", e64, e64);
    `checks(formatted, "8589934593/8589934593");
    n64 = 64'h0000_0000_0000_0001;
    formatted = $sformatf("%0p/%0p", n64, n64);
    `checks(formatted, {COMPACT_NUM_PREFIX, "1/", COMPACT_NUM_PREFIX, "1"});
    // Wide enums use names for %p/%s without changing explicit numeric formats.
    e96 = W96B;  // 10 * 2**64 + 1
    if (empty_no_opt != "") e96 = W96A;  // Defeat constant folding
    formatted = $sformatf("%p/%p", e96, e96);
    `checks(formatted, "W96B/W96B");
    formatted = $sformatf("%s/%s", e96, e96);
    `checks(formatted, "W96B/W96B");
    formatted = $sformatf("%0p/%0p", e96, e96);
    `checks(formatted, "W96B/W96B");
    formatted = $sformatf("%0d/%0d", e96, e96);
    `checks(formatted, "184467440737095516161/184467440737095516161");
    formatted = $sformatf("%0h/%0h", e96, e96);
    `checks(formatted, "a0000000000000001/a0000000000000001");
    // Exercise display/write-family formatting path in addition to $sformatf checks.
    $display("display-valid:%s:%0d:%p", e, 7, e);
    $write("write-valid:%s:%0d:%p\n", e, 8, e);
    // Invalid enum values fall back to numeric formatting for %p/%s.
    e = my_e'(3);
    formatted = $sformatf("%p/%p", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%P/%P", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%0p/%0p", e, e);
    `checks(formatted, {COMPACT_NUM_PREFIX, "3/", COMPACT_NUM_PREFIX, "3"});
    formatted = $sformatf("%s/%s", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%S/%S", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%4p/%4p", e, e);
`ifdef QUESTA
    `checks(formatted, "0003/0003");
`else
    `checks(formatted, "3/3");
`endif
    formatted = $sformatf("%4s/%4s", e, e);
    `checks(formatted, "   3/   3");
    formatted = $sformatf("%d/%d", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%0d/%0d", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%h/%h", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%0h/%0h", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%b/%b", e, e);
    `checks(formatted, "11/11");
    formatted = $sformatf("%0b/%0b", e, e);
    `checks(formatted, "11/11");
    formatted = $sformatf("%o/%o", e, e);
    `checks(formatted, "3/3");
    formatted = $sformatf("%x/%x", e, e);
    `checks(formatted, "3/3");
    // Non-terminal invalid-value fallback with mixed formatters.
    `checks($sformatf("%0d:%p:%0d", 9, e, 7), "9:3:7");
    `checks($sformatf("%s %h %p", e, 4'hA, e), "3 a 3");
    formatted = $sformatf("pre %% %s/%s post", e, e);
    `checks(formatted, "pre % 3/3 post");
    `checks($sformatf("%s|%p", e, e), "3|3");
    formatted = $sformatf("%s/%s", (1'b1 ? my_e'(3) : E0), (1'b1 ? my_e'(3) : E0));
    `checks(formatted, "3/3");
    formatted = $sformatf("%p/%p", (1'b0 ? E0 : my_e'(3)), (1'b0 ? E0 : my_e'(3)));
    `checks(formatted, "3/3");
    $display("display-invalid:%s:%0d:%p", e, 7, e);
    $write("write-invalid:%s:%0d:%p\n", e, 8, e);
    // Runtime-computed $sformatf formats should preserve enum mnemonic/fallback behavior.
    e = E2;
    fmt = {"%", "s/%s", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, "E2/E2");
    fmt = {"%", "p/%p", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, "E2/E2");
    fmt = {"%0h/%0h", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, "2/2");
    fmt = {"%0d:%", "s", ":%0d", empty_no_opt};
    `checks($sformatf(fmt, 9, e, 7), "9:E2:7");
    fmt = {"%", "s", " %h %", "p", empty_no_opt};
    `checks($sformatf(fmt, e, 4'hA, e), "E2 a E2");
    e = my_e'(3);
    fmt = {"%0b/%0b", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, "11/11");
    fmt = {"%", "s/%s", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, "3/3");
    fmt = {"%", "p/%p", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, "3/3");
    fmt = {"%0", "p/%0p", empty_no_opt};
    formatted = $sformatf(fmt, e, e);
    `checks(formatted, {COMPACT_NUM_PREFIX, "3/", COMPACT_NUM_PREFIX, "3"});
    fmt = {"%0d:%", "s", ":%0d", empty_no_opt};
    `checks($sformatf(fmt, 9, e, 7), "9:3:7");
    fmt = {"%", "s", " %h %", "p", empty_no_opt};
    `checks($sformatf(fmt, e, 4'hA, e), "3 a 3");
    fmt = {"%", "p/%p", empty_no_opt};
    formatted = $sformatf(fmt, e64, e64);
    `checks(formatted, "8589934593/8589934593");
    // Runtime formats must also preserve the wide enum's name.
    fmt = {"%", "p/%p", empty_no_opt};
    formatted = $sformatf(fmt, e96, e96);
    `checks(formatted, "W96B/W96B");
    fmt = {"%0d/%0d", empty_no_opt};
    formatted = $sformatf(fmt, e96, e96);
    `checks(formatted, "184467440737095516161/184467440737095516161");
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
    formatted = $sformatf("%c/%c", bitstream_value, bitstream_value);
    `checks(formatted, "A/A");
    // verilator lint_on WIDTHTRUNC

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
