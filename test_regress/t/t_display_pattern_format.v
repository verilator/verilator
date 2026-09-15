// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;
  bit clk = 0;
  always #5 clk = ~clk;
  int cyc = 0;
  typedef string text_t;
  typedef bit [6:0] narrow_array_t[2];
  typedef bit [64:0] wide_array_t[2];
  typedef enum logic [6:0] {
    FIRST = 7'd3,
    SECOND = 7'd65
  } enum_t;
  typedef enum_t enum_alias_t;
  typedef enum logic signed [6:0] {
    SIGNED7_NEG = -7'sd3,
    SIGNED7_POS = 7'sd7
  } signed7_t;
  typedef signed7_t signed7_alias_t;
  typedef enum logic signed [32:0] {
    SIGNED33_NEG = -33'sd3,
    SIGNED33_POS = 33'sd7
  } signed33_t;
  typedef enum logic signed [64:0] {
    SIGNED65_NEG = -65'sd18446744073709551615,
    SIGNED65_POS = 65'sd7
  } signed65_t;

  localparam text_t TEXT_PARAM = "quote=\" slash=\\ bell=\a form=\f vert=\v ctrl=\001";
  localparam string ESCAPED_PARAM_STRING = $sformatf("%p", TEXT_PARAM);
  localparam narrow_array_t NARROW_FIRST = '{7'd3, 7'd127};
  localparam narrow_array_t NARROW_SECOND = '{7'd65, 7'd9};
  localparam wide_array_t WIDE_FIRST = '{65'h10000000000000001, 65'h100000000};
  localparam wide_array_t WIDE_SECOND = '{65'h1ffffffffffffffff, 65'h200000003};
  localparam string NARROW_FIRST_TEXT = $sformatf("%p", NARROW_FIRST);
  localparam string NARROW_SECOND_TEXT = $sformatf("%p", NARROW_SECOND);
  localparam string WIDE_FIRST_TEXT = $sformatf("%p", WIDE_FIRST);
  localparam string WIDE_SECOND_TEXT = $sformatf("%p", WIDE_SECOND);
  localparam string REAL_FIRST_TEXT = $sformatf("%p", 1.25);
  localparam string REAL_SECOND_TEXT = $sformatf("%p", 0.5);

  initial begin
`ifdef QUESTA
    // Questa 2025.2 does not escape strings as required by IEEE 1800-2012 21.2.1.7.
    `checks(ESCAPED_PARAM_STRING, {"\"", TEXT_PARAM, "\""});
`else
    `checks(ESCAPED_PARAM_STRING,
            "\"quote=\\\" slash=\\\\ bell=\\007 form=\\014 vert=\\013 ctrl=\\001\"");
`endif
  end

  always @(posedge clk) begin
    text_t plain;
    string escaped;
    string escaped_expected;
    string fmt;
    enum_alias_t enum_value;
    narrow_array_t narrow;
    wide_array_t wide;
    real real_value;
    string array_expected;
    string real_expected;
    string formatted;
    string enum_text;
    signed7_alias_t signed7_value;
    signed33_t signed33_value;
    signed65_t signed65_value;
    string signed_expected;

    plain = $sformatf("round %0d", cyc);
    escaped = {"quote=\" slash=\\ line=\n cr=\r tab=\t bell=\a form=\f vert=\v ctrl=\001 ", plain};
`ifdef QUESTA
    escaped_expected = {"\"", escaped, "\""};
`else
    escaped_expected = {
      "\"quote=\\\" slash=\\\\ line=\\n cr=\\r tab=\\t bell=\\007 ",
      "form=\\014 vert=\\013 ctrl=\\001 ",
      plain,
      "\""
    };
`endif
    formatted = $sformatf("%p", plain);
    `checks(formatted, {"\"", plain, "\""});
    formatted = $sformatf("%p", escaped);
    `checks(formatted, escaped_expected);
    formatted = $sformatf("%s", escaped);
    `checks(formatted, escaped);
    fmt = cyc[0] ? "%p" : "%P";
    formatted = $sformatf(fmt, escaped);
    `checks(formatted, escaped_expected);
    plain = "";
    formatted = $sformatf("%p", plain);
    `checks(formatted, "\"\"");

    narrow = cyc[0] ? NARROW_SECOND : NARROW_FIRST;
    wide = cyc[0] ? WIDE_SECOND : WIDE_FIRST;

    // Pattern layout may vary by simulator; constant and runtime forms must agree.
    array_expected = cyc[0] ? NARROW_SECOND_TEXT : NARROW_FIRST_TEXT;
    formatted = $sformatf("%p", narrow);
    `checks(formatted, array_expected);
    formatted = $sformatf(fmt, narrow);
    `checks(formatted, array_expected);
    array_expected = cyc[0] ? WIDE_SECOND_TEXT : WIDE_FIRST_TEXT;
    formatted = $sformatf("%p", wide);
    `checks(formatted, array_expected);
    formatted = $sformatf(fmt, wide);
    `checks(formatted, array_expected);

    enum_value = cyc[0] ? SECOND : FIRST;

    // Identical enum conversions must compare correctly when merging the branches.
    if (cyc[0]) enum_text = $sformatf(fmt, enum_value);
    else enum_text = $sformatf(fmt, enum_value);

    `checks(enum_text, cyc[0] ? "SECOND" : "FIRST");
    formatted = $sformatf("%p", enum_value);
    `checks(formatted, enum_text);
    formatted = $sformatf("%s", enum_value);
    `checks(formatted, enum_text);

    real_value = cyc[0] ? 0.5 : 1.25;
    real_expected = cyc[0] ? REAL_SECOND_TEXT : REAL_FIRST_TEXT;
    formatted = $sformatf(fmt, real_value);
    `checks(formatted, real_expected);

    signed7_value = cyc[0] ? SIGNED7_NEG : signed7_t'(-7'sd2);
    signed33_value = cyc[0] ? SIGNED33_NEG : signed33_t'(-33'sd2);
    signed_expected = cyc[0] ? "-3" : "-2";
    formatted = $sformatf("%0d", signed7_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf("%0d", signed33_value);
    `checks(formatted, signed_expected);
    fmt = cyc[0] ? "%0d" : "%0D";
    formatted = $sformatf(fmt, signed7_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf(fmt, signed33_value);
    `checks(formatted, signed_expected);

    signed65_value = cyc[0] ? signed65_t'(-65'sd2) : SIGNED65_NEG;
    signed_expected = cyc[0] ? "-2" : "-18446744073709551615";
    formatted = $sformatf("%0d", signed65_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf(fmt, signed65_value);
    `checks(formatted, signed_expected);

    signed_expected = cyc[0] ? "SIGNED7_NEG" : "-2";
`ifdef QUESTA
    // Questa 2025.2 zero-extends unnamed enums narrower than 32 bits for %p/%s.
    if (!cyc[0]) signed_expected = "126";
`endif
    formatted = $sformatf("%p", signed7_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf("%s", signed7_value);
    `checks(formatted, signed_expected);
    fmt = cyc[1] ? "%p" : "%s";
    formatted = $sformatf(fmt, signed7_value);
    `checks(formatted, signed_expected);

    signed_expected = cyc[0] ? "SIGNED33_NEG" : "-2";
    formatted = $sformatf("%p", signed33_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf("%s", signed33_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf(fmt, signed33_value);
    `checks(formatted, signed_expected);

    cyc <= cyc + 1;
    if (cyc == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
