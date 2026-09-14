// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
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
  typedef enum logic signed [94:0] {
    SIGNED95_NEG = -95'sd19807040628566084398385987583,
    SIGNED95_POS = 95'sd1
  } signed95_t;
  typedef enum logic signed [128:0] {
    SIGNED129_LOW = 129'sd1,
    SIGNED129_HIGH = 129'sd18446744073709551617,
    SIGNED129_NEG = -129'sd340282366920938463463374607431768211455
  } signed129_t;
  typedef signed129_t signed129_alias_t;
  typedef enum logic [64:0] {
    UNSIGNED65_LOW = 65'h1,
    UNSIGNED65_HIGH = 65'h10000000000000001,
    \escaped.wide = 65'h3,
    UNSIGNED65_X = 65'bx
  } unsigned65_t;
  typedef unsigned65_t unsigned65_alias_t;

  int enum_calls = 0;
  function automatic unsigned65_t next_enum(input bit high);
    enum_calls++;
    return high ? UNSIGNED65_HIGH : UNSIGNED65_LOW;
  endfunction

  function automatic string format_enum(input unsigned65_t value);
    return $sformatf("%p/%s", value, value);
  endfunction

  function automatic string format_padded_decimal(input int value);
    return $sformatf("%04d", value);
  endfunction

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
  localparam string ENUM_LOW_TEXT = $sformatf("%p", UNSIGNED65_LOW);
  localparam string ENUM_HIGH_TEXT = $sformatf("%s", UNSIGNED65_HIGH);
  localparam string ENUM_NEG_TEXT = $sformatf("%p", SIGNED65_NEG);
  localparam string ENUM95_NEG_TEXT = $sformatf("%p", SIGNED95_NEG);
  localparam string ENUM95_POS_TEXT = $sformatf("%s", SIGNED95_POS);
  localparam string ENUM129_LOW_TEXT = $sformatf("%p", SIGNED129_LOW);
  localparam string ENUM129_HIGH_TEXT = $sformatf("%s", SIGNED129_HIGH);
  localparam string ENUM129_NEG_TEXT = $sformatf("%p", SIGNED129_NEG);
  localparam string ENUM_ESCAPED_TEXT = $sformatf("%p", \escaped.wide );
  localparam string ENUM_FUNC_TEXT = format_enum(UNSIGNED65_HIGH);
  localparam unsigned65_t ENUM_UNKNOWN = unsigned65_t'(65'h10000000000000002);
  localparam string ENUM_UNKNOWN_TEXT = $sformatf("%p", ENUM_UNKNOWN);
  localparam string ENUM_UNKNOWN_STRING = $sformatf("%s", ENUM_UNKNOWN);
  localparam string ENUM_UNKNOWN_COMPACT = $sformatf("%0p", ENUM_UNKNOWN);
  localparam string ENUM_UNKNOWN_FUNC_TEXT = format_enum(ENUM_UNKNOWN);
  localparam string ENUM_SIGNED_UNKNOWN_TEXT = $sformatf("%p", signed65_t'(-65'sd2));
  localparam string PADDED_CONST_TEXT = $sformatf("%04d", 32'd2);
  localparam string PADDED_FUNC_TEXT = format_padded_decimal(-2);
`ifdef QUESTA
  localparam string PADDED_POS_EXPECTED = "   2";
  localparam string PADDED_NEG2_EXPECTED = "  -2";
  localparam string PADDED_NEG3_EXPECTED = "  -3";
`else
  localparam string PADDED_POS_EXPECTED = "0002";
  localparam string PADDED_NEG2_EXPECTED = "-002";
  localparam string PADDED_NEG3_EXPECTED = "-003";
`endif

  initial begin
    string formatted;
    string fmt;
    `checks(PADDED_CONST_TEXT, PADDED_POS_EXPECTED);
    `checks(PADDED_FUNC_TEXT, PADDED_NEG2_EXPECTED);
`ifdef TEST_PROTECT
    formatted = ENUM_HIGH_TEXT.substr(0, 1);
    `checks(formatted, "PS");
    formatted = ENUM129_NEG_TEXT.substr(0, 1);
    `checks(formatted, "PS");
`else
    `checks(ENUM_LOW_TEXT, "UNSIGNED65_LOW");
    `checks(ENUM_HIGH_TEXT, "UNSIGNED65_HIGH");
    `checks(ENUM_NEG_TEXT, "SIGNED65_NEG");
    `checks(ENUM95_NEG_TEXT, "SIGNED95_NEG");
    `checks(ENUM95_POS_TEXT, "SIGNED95_POS");
    `checks(ENUM129_LOW_TEXT, "SIGNED129_LOW");
    `checks(ENUM129_HIGH_TEXT, "SIGNED129_HIGH");
    `checks(ENUM129_NEG_TEXT, "SIGNED129_NEG");
    `checks(ENUM_ESCAPED_TEXT, "\\escaped.wide ");
    `checks(ENUM_FUNC_TEXT, "UNSIGNED65_HIGH/UNSIGNED65_HIGH");
`endif
    `checks(ENUM_UNKNOWN_STRING, ENUM_UNKNOWN_TEXT);
    `checks(ENUM_UNKNOWN_FUNC_TEXT, {ENUM_UNKNOWN_TEXT, "/", ENUM_UNKNOWN_TEXT});
    `checks(ENUM_SIGNED_UNKNOWN_TEXT, "-2");
`ifdef QUESTA
    `checks(ENUM_UNKNOWN_TEXT, "2");
    `checks(ENUM_UNKNOWN_COMPACT, "2");
`else
    `checks(ENUM_UNKNOWN_TEXT, "18446744073709551618");
    `checks(ENUM_UNKNOWN_COMPACT, "'h10000000000000002");
`endif
    fmt = "%0h";
    formatted = $sformatf(fmt, UNSIGNED65_HIGH);
    `checks(formatted, "10000000000000001");
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
    signed95_t signed95_value;
    signed129_alias_t signed129_value;
    unsigned65_alias_t unsigned65_value;
    logic [64:0] unsigned65_bits;
    string signed_expected;
    string unsigned_expected;

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

    // The named values differ only above bit 63.
    unsigned65_value = cyc[0] ? UNSIGNED65_HIGH : UNSIGNED65_LOW;
    unsigned_expected = cyc[0] ? ENUM_HIGH_TEXT : ENUM_LOW_TEXT;
    formatted = $sformatf("%p", unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf("%s", unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf("%0p", unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, unsigned_expected);
    if (!$value$plusargs("enum_complement=%h", unsigned65_bits))
      unsigned65_bits = cyc[0] ? 65'h0fffffffffffffffe : 65'h1fffffffffffffffe;
    formatted = $sformatf("%p", unsigned65_t'(~unsigned65_bits));
    `checks(formatted, unsigned_expected);
    formatted = $sformatf(fmt, unsigned65_t'(~unsigned65_bits));
    `checks(formatted, unsigned_expected);
    formatted = format_enum(unsigned65_value);
    `checks(formatted, {unsigned_expected, "/", unsigned_expected});
    formatted = $sformatf("%0d:%p:%s:%0d", 9, unsigned65_value, signed65_value, 7);
    signed_expected = cyc[0] ? "-2" : ENUM_NEG_TEXT;
    `checks(formatted, {"9:", unsigned_expected, ":", signed_expected, ":7"});
    formatted = $sformatf("%p", signed65_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf("%s", signed65_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf(fmt, signed65_value);
    `checks(formatted, signed_expected);

    fmt = cyc[0] ? "%0d:%p:%s:%0d" : "%0d:%P:%S:%0d";
    formatted = $sformatf(fmt, 9, unsigned65_value, signed65_value, 7);
    `checks(formatted, {"9:", unsigned_expected, ":", signed_expected, ":7"});
    fmt = cyc[1] ? "%p" : "%s";
    enum_calls = 0;
    formatted = $sformatf("%p", next_enum(cyc[0]));
    `checks(formatted, unsigned_expected);
    `checkd(enum_calls, 1);
    formatted = $sformatf("%s", next_enum(cyc[0]));
    `checks(formatted, unsigned_expected);
    `checkd(enum_calls, 2);
    formatted = $sformatf(fmt, next_enum(cyc[0]));
    `checks(formatted, unsigned_expected);
    `checkd(enum_calls, 3);
    $sformat(formatted, "%p", next_enum(cyc[0]));
    `checks(formatted, unsigned_expected);
    `checkd(enum_calls, 4);
    $display("wide-enum: %p", next_enum(cyc[0]));
    `checkd(enum_calls, 5);

    unsigned65_value = cyc[0] ? UNSIGNED65_HIGH : \escaped.wide ;
    unsigned_expected = cyc[0] ? ENUM_HIGH_TEXT : ENUM_ESCAPED_TEXT;
    formatted = $sformatf("%p", unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf("%s", unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, unsigned_expected);
    fmt = cyc[0] ? "%20s" : "%-20s";
    enum_text = $sformatf(fmt, unsigned_expected);
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, enum_text);

    unsigned65_bits = unsigned65_value;
    unsigned_expected = $sformatf("%0h", unsigned65_bits);
    fmt = cyc[0] ? "%0h" : "%0H";
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, unsigned_expected);
    unsigned_expected = $sformatf("%0d", unsigned65_bits);
    fmt = cyc[0] ? "%0d" : "%0D";
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, unsigned_expected);

    unsigned65_value = unsigned65_t'(65'h10000000000000002 + 65'(cyc));
    unsigned65_bits = unsigned65_value;
    unsigned_expected = $sformatf("%0d", unsigned65_bits);
`ifdef QUESTA
    // Questa 2025.2 truncates unnamed wide enums to 64 bits for %p/%s.
    unsigned_expected = $sformatf("%0d", unsigned65_bits[63:0]);
`endif
    formatted = $sformatf("%p", unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf("%s", unsigned65_value);
    `checks(formatted, unsigned_expected);
    fmt = cyc[0] ? "%p" : "%s";
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, unsigned_expected);
    unsigned_expected = $sformatf("%0h", unsigned65_bits);
    fmt = cyc[0] ? "%0h" : "%0H";
    formatted = $sformatf(fmt, unsigned65_value);
    `checks(formatted, unsigned_expected);
    formatted = $sformatf("%0p", unsigned65_value);
`ifdef QUESTA
    unsigned_expected = $sformatf("%0d", unsigned65_bits[63:0]);
    `checks(formatted, unsigned_expected);
`else
    `checks(formatted, {"'h", unsigned_expected});
`endif

    // Match VCS/Xcelium zero padding; Questa uses IEEE 1800-2023 21.2.1.2 spaces.
    fmt = cyc[0] ? "%04d" : "%04D";
    signed_expected = cyc[0] ? PADDED_NEG3_EXPECTED : PADDED_NEG2_EXPECTED;
    formatted = $sformatf("%04d", signed7_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf(fmt, signed7_value);
    `checks(formatted, signed_expected);
    formatted = format_padded_decimal(cyc[0] ? -3 : -2);
    `checks(formatted, signed_expected);
    signed_expected = cyc[0] ? PADDED_NEG2_EXPECTED : "-18446744073709551615";
    formatted = $sformatf("%04d", signed65_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf(fmt, signed65_value);
    `checks(formatted, signed_expected);

    signed_expected = cyc[0] ? "  -3" : "  -2";
    formatted = $sformatf("%4d", signed7_value);
    `checks(formatted, signed_expected);
    signed_expected = cyc[0] ? "-3  " : "-2  ";
    formatted = $sformatf("%-04d", signed7_value);
    `checks(formatted, signed_expected);

    // Signed values sharing their low 64 bits must retain distinct names.
    signed95_value = cyc[0] ? SIGNED95_NEG : SIGNED95_POS;
    signed_expected = cyc[0] ? ENUM95_NEG_TEXT : ENUM95_POS_TEXT;
    formatted = $sformatf("%p", signed95_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf("%s", signed95_value);
    `checks(formatted, signed_expected);
    fmt = cyc[0] ? "%p" : "%s";
    formatted = $sformatf(fmt, signed95_value);
    `checks(formatted, signed_expected);
    signed_expected = cyc[0] ? "-19807040628566084398385987583" : "1";
    formatted = $sformatf("%0d", signed95_value);
    `checks(formatted, signed_expected);
    fmt = cyc[0] ? "%0d" : "%0D";
    formatted = $sformatf(fmt, signed95_value);
    `checks(formatted, signed_expected);

    signed129_value = cyc[1] ? SIGNED129_NEG : (cyc[0] ? SIGNED129_HIGH : SIGNED129_LOW);
    signed_expected = cyc[1] ? ENUM129_NEG_TEXT : (cyc[0] ? ENUM129_HIGH_TEXT : ENUM129_LOW_TEXT);
    formatted = $sformatf("%p", signed129_value);
    `checks(formatted, signed_expected);
    formatted = $sformatf("%s", signed129_value);
    `checks(formatted, signed_expected);
    fmt = cyc[0] ? "%p" : "%s";
    formatted = $sformatf(fmt, signed129_value);
    `checks(formatted, signed_expected);
    signed_expected = cyc[1] ? "-340282366920938463463374607431768211455" :
        (cyc[0] ? "18446744073709551617" : "1");
    formatted = $sformatf("%0d", signed129_value);
    `checks(formatted, signed_expected);
    fmt = cyc[0] ? "%0d" : "%0D";
    formatted = $sformatf(fmt, signed129_value);
    `checks(formatted, signed_expected);

    cyc <= cyc + 1;
    if (cyc == 3) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
