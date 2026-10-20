// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

typedef enum logic [1:0] {
  RED,
  GREEN,
  BLUE
} color_e;

typedef enum logic [31:0] {
  LOW = 32'h1,
  HIGH = 32'h1000_0000
} sparse_e;

package pkg;
  // Distinct type, but same values and names as '$unit::sparse_e', so same name map
  typedef enum logic [31:0] {
    LOW = 32'h1,
    HIGH = 32'h1000_0000
  } sparse_e;
endpackage

function automatic logic [31:0] getWord(logic [2:0] i);
  // Same value as 'WIDE' below
  localparam bit [255:0] WORDS = {
    32'h8888_8888,
    32'h7777_7777,
    32'h6666_6666,
    32'h5555_5555,
    32'h4444_4444,
    32'h3333_3333,
    32'h2222_2222,
    32'h1111_1111
  };
  return WORDS[32*i+:32];
endfunction

function automatic logic [7:0] getDigit(logic [3:0] d);
  localparam logic [7:0] DIGITS[10] = '{"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"};
  return DIGITS[d];
endfunction

function automatic string getName(logic [1:0] c);
  // Same as the enum name table: indexed by the enum value, empty for unused values
  localparam string NAMES[3:0] = '{"", "BLUE", "GREEN", "RED"};
  return NAMES[c];
endfunction

typedef int offsets_t[3:15];

function automatic offsets_t getOffsets(int base);
  offsets_t offsets;
  for (int i = 3; i <= 15; ++i) offsets[i] = base + i;
  return offsets;
endfunction

function automatic int getOffset(logic [3:0] i);
  // Value computed by a function, so it has the typedef'd type
  localparam offsets_t OFFSETS = getOffsets(100);
  return OFFSETS[i];
endfunction

typedef struct {
  logic [255:0] wide;
  int narrow;
} big_t;

typedef struct {
  int a;
  int b;
} smallStruct_t;

class Cls;
endclass

interface ifc;
endinterface

typedef struct {
  logic [255:0] wide;
  Cls obj;
  chandle ptr;
} handles_t;

// A member for each form a constant is emitted in
typedef struct {
  bit [255:0] wide;
  bit [7:0] small8;
  bit [7:0] hex8;
  bit [15:0] hex16;
  bit [31:0] hex32;
  int negative;
  bit [63:0] small64;
  bit [63:0] hex64;
  bit [95:0] words3;
  real realWhole;
  real realFraction;
  real realLarge;
  real realInf;
  real realNegInf;
  real realNan;
  real realNegNan;
  string strEmpty;
  string strControl;
  time timeValue;
  realtime realtimeValue;
  real realNegZero;
  bit oneBit;
  byte byteValue;
  shortint shortintValue;
  longint longintValue;
  integer integerValue;
  string strHigh;
} forms_t;

typedef struct {
  int a;
  int q[$];
} withQueue_t;

// Aggregates nested in a constant
typedef struct {
  bit [255:0] wide;
  int q[$];
  int d[];
  int m[int];
  int a[3];
  big_t s;
} nested_t;

module t;
  ifc i ();
  logic clk = 0;
  always #5 clk = ~clk;

  integer cyc = 0;
  color_e color;
  string names[3] = '{"RED", "GREEN", "BLUE"};
  sparse_e sparse;
  pkg::sparse_e pkgSparse;
  localparam bit [255:0] WIDE = {
    32'h8888_8888,
    32'h7777_7777,
    32'h6666_6666,
    32'h5555_5555,
    32'h4444_4444,
    32'h3333_3333,
    32'h2222_2222,
    32'h1111_1111
  };

  always @(posedge clk) begin
    cyc <= cyc + 1;
    color = color_e'(cyc % 3);
    `checks(color.name(), names[cyc%3]);
    `checks(getName(2'(cyc % 3)), names[cyc%3]);
    `checkh(getDigit(4'(cyc % 10)), 8'h30 + 8'(cyc % 10));
    `checkh(getOffset(4'(cyc % 13 + 3)), 100 + cyc % 13 + 3);
    sparse = cyc[0] ? HIGH : LOW;
    `checks(sparse.name(), cyc[0] ? "HIGH" : "LOW");
    pkgSparse = cyc[1] ? pkg::HIGH : pkg::LOW;
    `checks(pkgSparse.name(), cyc[1] ? "HIGH" : "LOW");
    `checkh(WIDE[32*(cyc%8)+:32], 32'h1111_1111 * (cyc % 8 + 1));
    `checkh(getWord(3'(cyc + 3)), 32'h1111_1111 * ((cyc + 3) % 8 + 1));
    begin
      int q[$];
      int qSame[$];
      int qSmall[$];
      int d[];
      int m[int];
      int w[*];
      big_t s;
      q = '{1, 2, 3, 4, 5, 6, 7, 8, 9};
      `checkh(q[cyc%9], cyc % 9 + 1);
      qSame = '{1, 2, 3, 4, 5, 6, 7, 8, 9};  // Same entry as 'q'
      `checkh(qSame[(cyc+1)%9], (cyc + 1) % 9 + 1);
      qSmall = '{1, 2};  // Small, but containers are always in the constant pool
      `checkh(qSmall[cyc%2], cyc % 2 + 1);
      d = '{1, 2, 3, 4, 5, 6, 7, 8, 9, 10};
      `checkh(d[cyc%10], cyc % 10 + 1);
      m = '{0: 1, 1: 2, 2: 3, 3: 4, 4: 5, 5: 6, 6: 7, 7: 8, 8: 9};
      `checkh(m[cyc%9], cyc % 9 + 1);
      w = '{0: 9, 1: 8, 2: 7, 3: 6, 4: 5, 5: 4, 6: 3, 7: 2, 8: 1};
      `checkh(w[cyc%9], 9 - cyc % 9);
      s = '{wide: {8{32'h1234_5678}}, narrow: 42};
      `checkh(s.wide[32*(cyc%8)+:32], 32'h1234_5678);
      `checkh(s.narrow, 42);
    end
    begin
      smallStruct_t ss;
      ss = '{a: 1, b: 2};  // Too small, so not in the constant pool
      `checkh(ss.a + ss.b, 3);
    end
    begin
      forms_t f;
      f = '{
          wide: {8{32'h89ab_cdef}},
          small8: 8'd5,
          hex8: 8'hab,
          hex16: 16'habcd,
          hex32: 32'h89ab_cdef,
          negative: -5,
          small64: 64'd3,
          hex64: 64'h0123_4567_89ab_cdef,
          words3: 96'h0123_4567_89ab_cdef_fedc_ba98,
          realWhole: 2.0,
          realFraction: 0.1,
          realLarge: 1.5e30,
          realInf: $bitstoreal(64'h7ff0_0000_0000_0000),
          realNegInf: $bitstoreal(64'hfff0_0000_0000_0000),
          realNan: $bitstoreal(64'h7ff8_0000_0000_0000),
          realNegNan: $bitstoreal(64'hfff8_0000_0000_0000),
          strEmpty: "",
          strControl: "a\tb\n\"q\"\\",
          timeValue: 64'h0000_0123_4567_89ab,
          realtimeValue: 2.5,
          realNegZero: -0.0,
          oneBit: 1'b1,
          byteValue: -8'sd3,
          shortintValue: -16'sd300,
          longintValue: -64'sd5,
          integerValue: -32'sd7,
          strHigh: {8'hff, 8'h80, "z"}
      };
      `checkh(f.wide[32*(cyc%8)+:32], 32'h89ab_cdef);
      `checkh(f.small8, 8'd5);
      `checkh(f.hex8, 8'hab);
      `checkh(f.hex16, 16'habcd);
      `checkh(f.hex32, 32'h89ab_cdef);
      `checkh(f.negative, -5);
      `checkh(f.small64, 64'd3);
      `checkh(f.hex64, 64'h0123_4567_89ab_cdef);
      `checkh(f.words3, 96'h0123_4567_89ab_cdef_fedc_ba98);
      `checkh($realtobits(f.realWhole), $realtobits(2.0));
      `checkh($realtobits(f.realFraction), $realtobits(0.1));
      `checkh($realtobits(f.realLarge), $realtobits(1.5e30));
      `checkh($realtobits(f.realInf), 64'h7ff0_0000_0000_0000);
      `checkh($realtobits(f.realNegInf), 64'hfff0_0000_0000_0000);
      if (f.realNan == f.realNan) $stop;
      if (f.realNegNan == f.realNegNan) $stop;
      `checkh($realtobits(f.realNegNan) >> 63, 64'd1);
      `checks(f.strEmpty, "");
      `checkh(f.strControl.len(), 8);
      `checks(f.strControl, {"a", 8'h09, "b", 8'h0a, 8'h22, "q", 8'h22, 8'h5c});
      `checkh(f.timeValue, 64'h0000_0123_4567_89ab);
      `checkh($realtobits(f.realtimeValue), $realtobits(2.5));
      `checkh($realtobits(f.realNegZero), 64'h8000_0000_0000_0000);
      `checkh(f.oneBit, 1'b1);
      `checkh(f.byteValue, -8'sd3);
      `checkh(f.shortintValue, -16'sd300);
      `checkh(f.longintValue, -64'sd5);
      `checkh(f.integerValue, -32'sd7);
      `checks(f.strHigh, {8'hff, 8'h80, "z"});
    end
    begin
      nested_t n;
      big_t bs[$];
      n = '{
          wide: {8{32'h1111_2222}},
          q: '{1, 2, 3},
          d: '{4, 5},
          m: '{1: 10, 2: 20},
          a: '{7, 8, 9},
          s: '{wide: {8{32'h3333_4444}}, narrow: 5}
      };
      `checkh(n.wide[32*(cyc%8)+:32], 32'h1111_2222);
      `checkh(n.q.size(), 3);
      `checkh(n.q[cyc%3], cyc % 3 + 1);
      `checkh(n.d[cyc%2], cyc % 2 + 4);
      `checkh(n.m[1], 10);
      `checkh(n.m[2], 20);
      `checkh(n.a[cyc%3], cyc % 3 + 7);
      `checkh(n.s.wide[32*(cyc%8)+:32], 32'h3333_4444);
      `checkh(n.s.narrow, 5);
      bs = '{'{wide: {8{32'h5555_6666}}, narrow: 1}, '{wide: {8{32'h7777_8888}}, narrow: 2}};
      `checkh(bs.size(), 2);
      `checkh(bs[0].wide[32*(cyc%8)+:32], 32'h5555_6666);
      `checkh(bs[1].narrow, 2);
    end
    begin
      withQueue_t wq;
      wq = '{a: 1, q: '{2, 3}};  // Small, but holds a container, so in the pool whole
      `checkh(wq.a, 1);
      `checkh(wq.q[cyc%2], cyc % 2 + 2);
      wq = '{a: cyc, q: '{4, 5, 6}};  // Not constant, so not in the pool, nor the queue
      `checkh(wq.a, cyc);
      `checkh(wq.q[cyc%3], cyc % 3 + 4);
    end
    begin  // Class references and chandles can only be null as a constant
      handles_t h;
      Cls objs[$];
      h = '{wide: {8{32'h1234_5678}}, obj: null, ptr: null};
      `checkh(h.wide[32*(cyc%8)+:32], 32'h1234_5678);
      if (h.obj != null) $stop;
      if (h.ptr != null) $stop;
      objs = '{null, null, null};
      if (objs.size() != 3) $stop;
      if (objs[cyc%3] != null) $stop;
    end
    begin  // Virtual interfaces too, here in a map with keys large enough for the pool
      virtual ifc ifcs[bit [255:0]];
      ifcs = '{256'h1: null, 256'h2: null};
      `checkh(ifcs.size(), 2);
      if (ifcs[256'h2] != null) $stop;
    end
    if (cyc == 20) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
