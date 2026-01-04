// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test case pattern matching with tagged unions
// IEEE 1800-2023 Section 12.6.1

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

  // Tagged union with nested structure (IEEE example)
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
    // Test 1: Basic case matches with void tag
    v = tagged Invalid;
    result = 0;
    case (v) matches
      tagged Invalid : result = 1;
      tagged Valid .n : result = n;
    endcase
    `checkh(result, 1);

    // Test 2: Case matches with value binding
    v = tagged Valid (123);
    result = 0;
    case (v) matches
      tagged Invalid : result = -1;
      tagged Valid .n : result = n;
    endcase
    `checkh(result, 123);

    // Test 3: Wide type case matching - 60-bit
    wt = tagged Wide60 (60'hFEDCBA987654321);
    wide60_result = 0;
    case (wt) matches
      tagged Invalid : wide60_result = 0;
      tagged Wide60 .w : wide60_result = w;
      default : wide60_result = 0;
    endcase
    `checkh(wide60_result, 60'hFEDCBA987654321);

    // Test 4: Wide type case matching - 90-bit
    wt = tagged Wide90 (90'hDE_ADBEEFCA_FEBABE12_3456);
    wide90_result = 0;
    case (wt) matches
      tagged Invalid : wide90_result = 0;
      tagged Wide90 .w : wide90_result = w;
      default : wide90_result = 0;
    endcase
    `checkh(wide90_result, 90'hDE_ADBEEFCA_FEBABE12_3456);

    // Test 5: Non-zero LSB case match
    wt = tagged Byte8NonZeroLSB (8'hA5);
    result = 0;
    case (wt) matches
      tagged Byte8NonZeroLSB .b : result = b;
      default : result = -1;
    endcase
    `checkh(result, 8'hA5);

    // Test 6: Opposite endianness case match
    wt = tagged Word32LittleEndian (32'hDEADBEEF);
    result = 0;
    case (wt) matches
      tagged Word32LittleEndian .w : result = w;
      default : result = -1;
    endcase
    `checkh(result, 32'hDEADBEEF);

    // Test 7: Array type case matching
    at = tagged Arr '{10, 20, 30, 40};
    result = 0;
    case (at) matches
      tagged Invalid : result = -1;
      tagged Scalar .s : result = s;
      tagged Arr .a : result = a[0] + a[1] + a[2] + a[3];
    endcase
    `checkh(result, 100);

    // Test 8: Nested tagged union case matching
    instr = tagged Jmp (tagged JmpC '{2'd1, 10'd256});
    result = 0;
    case (instr) matches
      tagged Add .* : result = -1;
      tagged Jmp (tagged JmpU .a) : result = a;
      tagged Jmp (tagged JmpC '{cc:.c, addr:.a}) : result = a;
    endcase
    `checkh(result, 256);

    // Test 9: Chandle case matching (no binding - VCS limitation)
    cht = tagged Invalid;
    result = 0;
    case (cht) matches
      tagged Invalid : result = 1;
      tagged Handle .* : result = 2;  // Wildcard - can't bind chandle
    endcase
    `checkh(result, 1);

    // Test 10: Class reference case matching
    obj = new(42);
    clt = tagged Obj (obj);
    result = 0;
    case (clt) matches
      tagged Invalid : result = -1;
      tagged Obj .o : result = o.value;
    endcase
    `checkh(result, 42);

    // Test 11: Real member case matching
    rt = tagged Invalid;
    result = 0;
    case (rt) matches
      tagged Invalid : result = 1;
      tagged RealVal .r : result = 2;
      tagged ShortRealVal .r : result = 3;
    endcase
    `checkh(result, 1);

    rt = tagged RealVal (3.14159);
    result = 0;
    case (rt) matches
      tagged Invalid : result = -1;
      tagged RealVal .r : begin
        if (r == 3.14159) result = 1;
        else result = 2;
      end
      tagged ShortRealVal .r : result = 3;
    endcase
    `checkh(result, 1);

    // Test 12: Shortreal member case matching
    rt = tagged ShortRealVal (2.5);
    result = 0;
    case (rt) matches
      tagged Invalid : result = -1;
      tagged RealVal .r : result = 2;
      tagged ShortRealVal .r : begin
        if (r == 2.5) result = 1;
        else result = 3;
      end
    endcase
    `checkh(result, 1);

    // Test 13: String member case matching
    st = tagged Invalid;
    result = 0;
    case (st) matches
      tagged Invalid : result = 1;
      tagged StrVal .s : result = 2;
    endcase
    `checkh(result, 1);

    st = tagged StrVal ("hello");
    result = 0;
    case (st) matches
      tagged Invalid : result = -1;
      tagged StrVal .s : begin
        if (s == "hello") result = 1;
        else result = 2;
      end
    endcase
    `checkh(result, 1);

    // Test 14: Enum member case matching
    et = tagged Invalid;
    result = 0;
    case (et) matches
      tagged Invalid : result = 1;
      tagged ColorVal .c : result = 2;
    endcase
    `checkh(result, 1);

    et = tagged ColorVal (GREEN);
    result = 0;
    case (et) matches
      tagged Invalid : result = -1;
      tagged ColorVal .c : begin
        if (c == GREEN) result = 1;
        else result = 2;
      end
    endcase
    `checkh(result, 1);

`ifndef VCS
    // Test 15: Event member case matching
    evt = tagged Invalid;
    result = 0;
    case (evt) matches
      tagged Invalid : result = 1;
      tagged EvtVal .* : result = 2;
    endcase
    `checkh(result, 1);
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
