// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2024 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilator lint_off SHORTREAL

// Test tagged union declaration, expressions, and member access
// IEEE 1800-2023 Sections 7.3.2, 11.9
// This test focuses on unpacked tagged unions with dynamic types

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

  // Tagged union with real/shortreal members (dynamic types)
  typedef union tagged {
    void      Invalid;
    real      RealVal;
    shortreal ShortRealVal;
  } RealType;

  // Tagged union with string member (dynamic type)
  typedef union tagged {
    void   Invalid;
    string StrVal;
  } StringType;

  // Tagged union with class reference member (dynamic type)
  typedef union tagged {
    void      Invalid;
    TestClass Obj;
  } ClassType;

  // Tagged union with chandle member (dynamic type)
  typedef union tagged {
    void    Invalid;
    chandle Handle;
  } ChandleType;

  RealType rt;
  StringType st;
  ClassType clt;
  TestClass obj;
  ChandleType cht;

  initial begin
    // Test 1: Real member
    rt = tagged Invalid;
    rt = tagged RealVal (3.14159);
    if (rt.RealVal != 3.14159) $stop;

    // Test 2: Shortreal member
    rt = tagged ShortRealVal (2.5);
    if (rt.ShortRealVal != 2.5) $stop;

    // Test 3: String member
    st = tagged Invalid;
    st = tagged StrVal ("hello");
    if (st.StrVal != "hello") $stop;

    // Test 4: Class reference member
    obj = new(42);
    clt = tagged Invalid;
    clt = tagged Obj (obj);
    `checkh(clt.Obj.value, 42);

    // Test 5: Chandle member
    cht = tagged Invalid;
    cht = tagged Handle (null);

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
