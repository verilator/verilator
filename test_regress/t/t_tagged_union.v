// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// Test tagged union declaration, expressions, and member access
// IEEE 1800-2023 Sections 7.3.2, 11.9

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

  // Basic tagged union with void and int (IEEE example)
  typedef union tagged {
    void Invalid;
    int Valid;
  } VInt;

  // Tagged union with multiple data types including wide types
  // Tests: non-zero LSBs, 60-bit (33-64 range), 90-bit (64+ range), opposite endianness
  typedef union tagged packed {
    void          Invalid;
    int           IntVal;
    shortint      ShortVal;
    longint       LongVal;
    byte          ByteVal;
    bit           BitVal;
    logic         LogicVal;
    bit [8:1]     Byte8NonZeroLSB;      // Non-zero LSB
    bit [16:1]    Word16NonZeroLSB;     // Non-zero LSB
    bit [0:31]    Word32LittleEndian;   // Opposite endianness
    bit [0:15]    Word16LittleEndian;   // Opposite endianness
    bit [59:0]    Wide60;               // 60-bit (33-64 special handling)
    bit [89:0]    Wide90;               // 90-bit (64+ special handling)
    bit [63:4]    Wide60NonZeroLSB;     // 60-bit with non-zero LSB
    bit [99:10]   Wide90NonZeroLSB;     // 90-bit with non-zero LSB
    bit [0:59]    Wide60LittleEndian;   // 60-bit opposite endianness
    bit [0:89]    Wide90LittleEndian;   // 90-bit opposite endianness
  } MultiType;

  // Tagged union with unpacked array members
  typedef union tagged {
    void           Invalid;
    int            Scalar;
    int            UnpackedArr[4];      // Unpacked array
    bit [31:0]     UnpackedArr2D[2][3]; // 2D unpacked array
  } ArrayType;

  // Tagged union with nested struct (IEEE example)
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

  VInt vi1, vi2;
  MultiType mt;
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

  initial begin
    // Test 1: Basic void member
    vi1 = tagged Invalid;
    vi2 = tagged Invalid;

    // Test 2: Basic value member
    vi1 = tagged Valid (42);
    `checkh(vi1.Valid, 42);

    vi2 = tagged Valid (23 + 34);
    `checkh(vi2.Valid, 57);

    // Test 3: MultiType with various data types
    mt = tagged Invalid;

    mt = tagged IntVal (32'h12345678);
    `checkh(mt.IntVal, 32'h12345678);

    mt = tagged ShortVal (16'hABCD);
    `checkh(mt.ShortVal, 16'hABCD);

    mt = tagged ByteVal (8'h5A);
    `checkh(mt.ByteVal, 8'h5A);

    mt = tagged BitVal (1'b1);
    `checkh(mt.BitVal, 1'b1);

    // Test 4: Non-zero LSB types
    mt = tagged Byte8NonZeroLSB (8'hA5);
    `checkh(mt.Byte8NonZeroLSB, 8'hA5);

    mt = tagged Word16NonZeroLSB (16'h1234);
    `checkh(mt.Word16NonZeroLSB, 16'h1234);

    // Test 5: Opposite endianness (little-endian style ranges)
    mt = tagged Word32LittleEndian (32'hDEADBEEF);
    `checkh(mt.Word32LittleEndian, 32'hDEADBEEF);

    mt = tagged Word16LittleEndian (16'hCAFE);
    `checkh(mt.Word16LittleEndian, 16'hCAFE);

    // Test 6: Wide types (60-bit, in 33-64 range)
    mt = tagged Wide60 (60'hFEDCBA987654321);
    `checkh(mt.Wide60, 60'hFEDCBA987654321);

    mt = tagged Wide60NonZeroLSB (60'h123456789ABCDEF);
    `checkh(mt.Wide60NonZeroLSB, 60'h123456789ABCDEF);

    mt = tagged Wide60LittleEndian (60'hABCDEF012345678);
    `checkh(mt.Wide60LittleEndian, 60'hABCDEF012345678);

    // Test 7: Wide types (90-bit, in 64+ range)
    mt = tagged Wide90 (90'hFF_FFFFFFFF_FFFFFFFF_FFFF);
    `checkh(mt.Wide90, 90'hFF_FFFFFFFF_FFFFFFFF_FFFF);

    mt = tagged Wide90NonZeroLSB (90'hDE_ADBEEFCA_FEBABE12_3456);
    `checkh(mt.Wide90NonZeroLSB, 90'hDE_ADBEEFCA_FEBABE12_3456);

    mt = tagged Wide90LittleEndian (90'h11_11111122_22222233_3333);
    `checkh(mt.Wide90LittleEndian, 90'h11_11111122_22222233_3333);

    // Test 8: Unpacked array members
    at = tagged Invalid;

    at = tagged Scalar (999);
    `checkh(at.Scalar, 999);

    at = tagged UnpackedArr '{100, 200, 300, 400};
    `checkh(at.UnpackedArr[0], 100);
    `checkh(at.UnpackedArr[1], 200);
    `checkh(at.UnpackedArr[2], 300);
    `checkh(at.UnpackedArr[3], 400);

    at = tagged UnpackedArr2D '{'{32'hA, 32'hB, 32'hC}, '{32'hD, 32'hE, 32'hF}};
    `checkh(at.UnpackedArr2D[0][0], 32'hA);
    `checkh(at.UnpackedArr2D[0][1], 32'hB);
    `checkh(at.UnpackedArr2D[0][2], 32'hC);
    `checkh(at.UnpackedArr2D[1][0], 32'hD);
    `checkh(at.UnpackedArr2D[1][1], 32'hE);
    `checkh(at.UnpackedArr2D[1][2], 32'hF);

    // Test 9: Nested tagged union (Instr example from IEEE)
    instr = tagged Add '{5'd1, 5'd2, 5'd3};
    `checkh(instr.Add.reg1, 5'd1);
    `checkh(instr.Add.reg2, 5'd2);
    `checkh(instr.Add.regd, 5'd3);

    // Create Add with named struct fields
    instr = tagged Add '{reg2:5'd10, regd:5'd20, reg1:5'd5};
    `checkh(instr.Add.reg1, 5'd5);
    `checkh(instr.Add.reg2, 5'd10);
    `checkh(instr.Add.regd, 5'd20);

    // Test 10: Nested tagged union - unconditional jump
    instr = tagged Jmp (tagged JmpU 10'd512);
    `checkh(instr.Jmp.JmpU, 10'd512);

    // Test 11: Nested tagged union - conditional jump
    instr = tagged Jmp (tagged JmpC '{2'd1, 10'd256});
    `checkh(instr.Jmp.JmpC.cc, 2'd1);
    `checkh(instr.Jmp.JmpC.addr, 10'd256);

    // Test 12: Nested tagged union - conditional jump with named fields
    instr = tagged Jmp (tagged JmpC '{cc:2'd3, addr:10'd100});
    `checkh(instr.Jmp.JmpC.cc, 2'd3);
    `checkh(instr.Jmp.JmpC.addr, 10'd100);

    // Test 13: Chandle member
    cht = tagged Invalid;
    cht = tagged Handle (null);

    // Test 14: Class reference member
    obj = new(42);
    clt = tagged Invalid;
    clt = tagged Obj (obj);
    `checkh(clt.Obj.value, 42);

    // Test 15: Real member
    rt = tagged Invalid;
    rt = tagged RealVal (3.14159);
    if (rt.RealVal != 3.14159) $stop;

    // Test 16: Shortreal member
    rt = tagged ShortRealVal (2.5);
    if (rt.ShortRealVal != 2.5) $stop;

    // Test 17: String member
    st = tagged Invalid;
    st = tagged StrVal ("hello");
    if (st.StrVal != "hello") $stop;

    // Test 18: Enum member
    et = tagged Invalid;
    et = tagged ColorVal (GREEN);
    if (et.ColorVal != GREEN) $stop;

`ifndef VCS
    // Test 19: Event member
    evt = tagged Invalid;
`endif

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
