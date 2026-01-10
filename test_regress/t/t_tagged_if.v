// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test if pattern matching with tagged unions
// IEEE 1800-2023 Section 12.6.2

// Class for testing class references in tagged unions
class TestClass;
  int value;
  function new(int v);
    value = v;
  endfunction
endclass

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0x exp=%0x (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);

module t;

  // Basic tagged union (IEEE example)
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  // Tagged union with wide types
  typedef union tagged packed {
    void          Invalid;
    bit [8:1]     Byte8NonZeroLSB;      // Non-zero LSB
    bit [0:31]    Word32LittleEndian;   // Opposite endianness
    bit [59:0]    Wide60;               // 60-bit (33-64 special handling)
    bit [89:0]    Wide90;               // 90-bit (64+ special handling)
  } WideType;

  // Tagged union with unpacked array
  typedef union tagged {
    void        Invalid;
    int         Scalar;
    int         Arr[4];                 // Unpacked array
  } ArrayType;

  // Tagged union with nested structure
  typedef union tagged {
    struct {
      bit [4:0] reg1, reg2, regd;
    } Add;
    union tagged {
      bit [9:0] JmpU;
      struct {
        bit [1:0] cc;
        bit [9:0] addr;
      } JmpC;
    } Jmp;
  } Instr;

  // Tagged union with chandle member
  typedef union tagged {
    void    Invalid;
    chandle Handle;
  } ChandleType;

  // Tagged union with class reference member
  typedef union tagged {
    void      Invalid;
    TestClass Obj;
  } ClassType;

  // Enum for testing enum members
  typedef enum {RED, GREEN, BLUE} Color;

  // Tagged union with real/shortreal members
  typedef union tagged {
    void      Invalid;
    real      RealVal;
    shortreal ShortRealVal;
  } RealType;

  // Tagged union with string member
  typedef union tagged {
    void   Invalid;
    string StrVal;
  } StringType;

  // Tagged union with enum member
  typedef union tagged {
    void  Invalid;
    Color ColorVal;
  } EnumType;

`ifndef VCS
  // Tagged union with event member
  // Note: VCS incorrectly reports "the event data type is not allowed in structures and unions"
  // but IEEE 1800-2023 does not prohibit this
  typedef union tagged {
    void  Invalid;
    event EvtVal;
  } EventType;
`endif

  VInt v;
  WideType wt;
  ArrayType at;
  Instr instr;
  ChandleType cht;
  ClassType clt;
  TestClass obj;
  RealType rt;
  StringType st;
  EnumType et;
`ifndef VCS
  EventType evt;
`endif
  int result;
  bit [59:0] wide60_result;
  bit [89:0] wide90_result;

  initial begin
    // Test 1: Basic if matches - void tag
    v = tagged Invalid;
    result = 0;
    if (v matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    // Test 2: Basic if matches - value with binding
    v = tagged Valid (42);
    result = 0;
    if (v matches tagged Valid .n)
      result = n;
    else
      result = -1;
    `checkh(result, 42);

    // Test 3: if-else chain
    v = tagged Valid (100);
    result = 0;
    if (v matches tagged Invalid)
      result = 1;
    else if (v matches tagged Valid .n)
      result = n;
    `checkh(result, 100);

    // Test 4: Wide type if matching - 60-bit
    wt = tagged Wide60 (60'hFEDCBA987654321);
    wide60_result = 0;
    if (wt matches tagged Wide60 .w)
      wide60_result = w;
    else
      wide60_result = 0;
    `checkh(wide60_result, 60'hFEDCBA987654321);

    // Test 5: Wide type if matching - 90-bit
    wt = tagged Wide90 (90'hDE_ADBEEFCA_FEBABE12_3456);
    wide90_result = 0;
    if (wt matches tagged Wide90 .w)
      wide90_result = w;
    else
      wide90_result = 0;
    `checkh(wide90_result, 90'hDE_ADBEEFCA_FEBABE12_3456);

    // Test 6: Non-zero LSB if match
    wt = tagged Byte8NonZeroLSB (8'hA5);
    result = 0;
    if (wt matches tagged Byte8NonZeroLSB .b)
      result = b;
    else
      result = -1;
    `checkh(result, 8'hA5);

    // Test 7: Opposite endianness if match
    wt = tagged Word32LittleEndian (32'hDEADBEEF);
    result = 0;
    if (wt matches tagged Word32LittleEndian .w)
      result = w;
    else
      result = -1;
    `checkh(result, 32'hDEADBEEF);

    // Test 8: Array type if matching
    at = tagged Arr '{10, 20, 30, 40};
    result = 0;
    if (at matches tagged Arr .a)
      result = a[0] + a[1] + a[2] + a[3];
    else
      result = -1;
    `checkh(result, 100);

    // Test 9: Array type scalar if match
    at = tagged Scalar (999);
    result = 0;
    if (at matches tagged Scalar .s)
      result = s;
    else
      result = -1;
    `checkh(result, 999);

    // Test 10: Nested pattern matching (IEEE example)
    instr = tagged Jmp (tagged JmpC '{2'd1, 10'd256});
    result = 0;
    if (instr matches tagged Jmp (tagged JmpC '{cc:.c, addr:.a}))
      result = a;  // 'a' is bound in pattern
    else
      result = -1;
    `checkh(result, 256);

    // Test 11: Chained matches with &&& (IEEE example)
    instr = tagged Jmp (tagged JmpC '{2'd2, 10'd128});
    result = 0;
    if (instr matches tagged Jmp .j &&&
       j matches tagged JmpC '{cc:.c, addr:.a})
      result = a;  // 'a' bound from second pattern
    else
      result = -1;
    `checkh(result, 128);

    // Test 12: Pattern with boolean filter expression
    v = tagged Valid (75);
    result = 0;
    if (v matches tagged Valid .n &&& (n > 50))
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    // Test 13: Pattern with boolean filter - no match
    v = tagged Valid (25);
    result = 0;
    if (v matches tagged Valid .n &&& (n > 50))
      result = 1;
    else
      result = 2;
    `checkh(result, 2);

    // Test 14: Scope test - bound variable only in true branch
    v = tagged Valid (99);
    result = 0;
    if (v matches tagged Valid .x) begin
      result = x;  // x is in scope here
    end
    // x is NOT in scope here (else branch / after)
    `checkh(result, 99);

    // Test 15: Add instruction matching
    instr = tagged Add '{5'd10, 5'd20, 5'd30};
    result = 0;
    if (instr matches tagged Add '{.r1, .r2, .rd})
      result = r1 + r2 + rd;
    else
      result = -1;
    `checkh(result, 60);

    // Test 16: Complex filter with register file simulation
    instr = tagged Jmp (tagged JmpC '{2'd3, 10'd100});
    result = 0;
    // If conditional jump and condition register is non-zero
    // Use nested if for boolean filter (VCS limitation with &&& after chained matches)
    if (instr matches tagged Jmp .j &&&
       j matches tagged JmpC '{cc:.c, addr:.a}) begin
      if (c != 0)
        result = a;
      else
        result = -1;
    end else
      result = -1;
    `checkh(result, 100);

    // Test 17: Unconditional jump matching
    instr = tagged Jmp (tagged JmpU 10'd512);
    result = 0;
    if (instr matches tagged Jmp (tagged JmpU .a))
      result = a;
    else
      result = -1;
    `checkh(result, 512);

    // Test 18: Wildcard pattern in if
    instr = tagged Add '{5'd1, 5'd2, 5'd3};
    result = 0;
    if (instr matches tagged Add .*)
      result = 1;
    else if (instr matches tagged Jmp .*)
      result = 2;
    `checkh(result, 1);

    // Test 19: Chandle member if matching
    cht = tagged Invalid;
    result = 0;
    if (cht matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    cht = tagged Handle (null);
    result = 0;
    if (cht matches tagged Handle .*)  // Wildcard - VCS can't bind chandle
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    // Test 20: Class reference member if matching
    obj = new(42);
    clt = tagged Invalid;
    result = 0;
    if (clt matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    clt = tagged Obj (obj);
    result = 0;
    if (clt matches tagged Obj .o)
      result = o.value;
    else
      result = -1;
    `checkh(result, 42);

    // Test 21: Real member if matching
    rt = tagged Invalid;
    result = 0;
    if (rt matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    rt = tagged RealVal (3.14159);
    result = 0;
    if (rt matches tagged RealVal .r) begin
      if (r == 3.14159)
        result = 1;
      else
        result = 2;
    end else
      result = -1;
    `checkh(result, 1);

    // Test 22: Shortreal member if matching
    rt = tagged ShortRealVal (2.5);
    result = 0;
    if (rt matches tagged ShortRealVal .r) begin
      if (r == 2.5)
        result = 1;
      else
        result = 2;
    end else
      result = -1;
    `checkh(result, 1);

    // Test 23: String member if matching
    st = tagged Invalid;
    result = 0;
    if (st matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    st = tagged StrVal ("hello");
    result = 0;
    if (st matches tagged StrVal .s) begin
      if (s == "hello")
        result = 1;
      else
        result = 2;
    end else
      result = -1;
    `checkh(result, 1);

    // Test 24: Enum member if matching
    et = tagged Invalid;
    result = 0;
    if (et matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);

    et = tagged ColorVal (GREEN);
    result = 0;
    if (et matches tagged ColorVal .c) begin
      if (c == GREEN)
        result = 1;
      else
        result = 2;
    end else
      result = -1;
    `checkh(result, 1);

`ifndef VCS
    // Test 25: Event member if matching
    evt = tagged Invalid;
    result = 0;
    if (evt matches tagged Invalid)
      result = 1;
    else
      result = 2;
    `checkh(result, 1);
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
