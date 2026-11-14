// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

// Test the "pick an unused ID" idiom: a rand index into a
// non-rand array must stay symbolic in the solver, not fold to a constant.

class UniqueIdPool;
  rand int id;
  bit used[16];

  constraint c_range { id inside {[0:15]}; }
  constraint c_unused { !used[id]; }
endclass

// Same idiom, reached via a member select on another object.
class Holder;
  bit used[16];
endclass

class UniqueIdPoolViaMember;
  rand int id;
  Holder holder;

  constraint c_range { id inside {[0:15]}; }
  constraint c_unused { !holder.used[id]; }

  function new();
    holder = new;
  endfunction
endclass

// Same idiom, but the array has a non-zero declared range ([1:16]).
class UniqueIdPoolNonZeroBase;
  rand int id;
  bit used[1:16];

  constraint c_range { id inside {[1:16]}; }
  constraint c_unused { !used[id]; }
endclass

// Same, but the declared range runs the opposite direction ([16:1]).
class UniqueIdPoolDescBase;
  rand int id;
  bit used[16:1];

  constraint c_range { id inside {[1:16]}; }
  constraint c_unused { !used[id]; }
endclass

// A rand array indexed by a rand value: unaffected by this fix, kept
// here for coverage of the "array is rand" path.
class RandArrayRandIndex;
  rand int idx;
  rand bit [7:0] data[4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx] == 8'hAA; }
endclass

// Same, but the rand array is multidimensional.
class RandMultidimRandIndex;
  rand int idx;
  rand bit [7:0] data[4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx][0] == 8'hAA; }
endclass

// Same, but the rand index is the outer subscript instead of the inner one --
// reaching the rand base variable through a nested array select, not a direct one.
class RandMultidimRandIndexOuter;
  rand int idx;
  rand bit [7:0] data[4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[0][idx] == 8'hAA; }
endclass

// Same shape at the exact 2x2 size the regression was originally reported
// at, distinct from the 4x4 case above.
class RandMultidimRandIndexOuterMinimal;
  rand int idx;
  rand bit [7:0] data[2][2];
  constraint c_idx { idx inside {[0:1]}; }
  constraint c_data { data[0][idx] == 8'hAA; }
endclass

// Same, but three dimensions deep with the rand index outermost -- the array's
// root must resolve through two nested index selects to reach the base array,
// not just one as in the two-dimensional case above.
class RandMultidimRandIndexDeep;
  rand int idx;
  rand bit [7:0] data[4][4][4];
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[1][2][idx] == 8'hAA; }
endclass

// Same idiom again, but the rand array is a queue directly rather than a
// fixed array.
class RandQueueRandIndex;
  rand bit data[$];
  rand int idx;
  constraint c_size { data.size() == 4; }
  constraint c_idx { idx inside {[0:3]}; }
  constraint c_data { data[idx] == 1; }
endclass

// An out-of-range index reads as 0 (IEEE 1800-2023 7.4.5), not as the last
// element -- an index equal to the size is only satisfiable if the solver
// models that default correctly.
class OutOfBoundsIndex;
  rand int idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx == 3; used[idx] == 0; }
endclass

// Same, but the index runs negative instead of past the top.
class OutOfBoundsIndexNegative;
  rand int idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx == -1; used[idx] == 0; }
endclass

// Same idea on a non-zero-based declared range, where the index is
// bias-adjusted before comparison -- the default must still apply once
// it falls outside [1:3], not just outside [0:2].
class OutOfBoundsIndexNonZeroBase;
  rand int idx;
  bit used[1:3] = '{1, 1, 1};
  constraint c { idx == 4; used[idx] == 0; }
endclass

// Same, but the index is wide enough to alias back into range if truncated to
// the array's 2-bit index width (4 reads element 0, 5 reads element 1).
class OutOfBoundsIndexPastIndexWidth;
  rand int idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx inside {[4:5]}; used[idx] == 0; }
endclass

// An explicit [1:0] part-select does truncate, so 4 reads element 0.
class ExplicitlyTruncatedIndex;
  rand int idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx == 4; used[idx[1:0]] == 0; }
endclass

// The index is exactly the array's index width, so there's no truncation.
class ExactWidthIndex;
  rand bit [1:0] idx;
  bit used[4] = '{1, 1, 0, 1};
  constraint c { used[idx] == 0; }
endclass

// An inline randomize() with spells the rand index as a member reference, which
// must keep the index's own width (a match past the truncation boundary is the guard).
class InlineWithPool;
  rand int idx;
  bit [7:0] pool[4];
  function new(); pool = '{8'h11, 8'h22, 8'h33, 8'h44}; endfunction
endclass

// The bias subtraction must sign-extend through user arithmetic, so -1 + 6
// reads element 5, not element 261.
class CompoundBiasIndex;
  rand byte r;
  bit [7:0] pool[5:12];
  constraint c { r == -1; pool[r+6] == 8'hB0; }
  function new();
    pool = '{8'hB0, 8'hB1, 8'hB2, 8'hB3, 8'hB4, 8'hB5, 8'hB6, 8'hB7};
  endfunction
endclass

// Same, but the zero-extended alias lands in range: UNSAT must stay UNSAT.
class CompoundBiasIndexUnsat;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == -1; pool[r+6] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[261] = 8'h77;
  endfunction
endclass

// A negation below the bias keeps its sign, so -(-6) reads element 6.
class NegateBiasIndex;
  rand byte r;
  bit [7:0] pool[5:12];
  constraint c { r == -6; pool[-r] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Same for bitwise inversion: ~(-7) reads element 6.
class BitwiseNotBiasIndex;
  rand byte r;
  bit [7:0] pool[5:12];
  constraint c { r == -7; pool[~r] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Multiplication below the bias is signed: (-2)*(-3) reads element 6.
class MultBiasIndex;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:12];
  constraint c { r1 == -2; r2 == -3; pool[r1*r2] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Same, but the zero-extended alias lands in range: UNSAT must stay UNSAT.
class MultBiasIndexUnsat;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:270];
  constraint c { r1 == -1; r2 == 1; pool[r1*r2] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[255] = 8'h77;
  endfunction
endclass

// Division below the bias is signed: (-12)/(-2) reads element 6.
class DivBiasIndex;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:12];
  constraint c { r1 == -12; r2 == -2; pool[r1/r2] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Same, but the zero-extended alias lands in range: UNSAT must stay UNSAT.
class DivBiasIndexUnsat;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:270];
  constraint c { r1 == -1; r2 == 1; pool[r1/r2] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[255] = 8'h77;
  endfunction
endclass

// Full-width operands divide signed too: (-12)/(-2) reads element 6.
class IntDivBiasIndex;
  rand int r1;
  rand int r2;
  bit [7:0] pool[5:12];
  constraint c { r1 == -12; r2 == -2; pool[r1/r2] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Unsigned operands divide unsigned: 12/2 reads element 6.
class UnsDivBiasIndex;
  rand bit [7:0] u1;
  rand bit [7:0] u2;
  bit [7:0] pool[5:12];
  constraint c { u1 == 12; u2 == 2; pool[u1/u2] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A left shift wider than its operand wraps: 16<<4 is 0, out of range.
class ShiftLeftWrapUnsat;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == 16; pool[r<<4] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[256] = 8'h77;
  endfunction
endclass

// Same shape without overflow: 1<<4 reads element 16.
class ShiftLeftBiasIndex;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == 1; pool[r<<4] == 8'hB0; }
  function new();
    pool[16] = 8'hB0;
  endfunction
endclass

// A shifted negative stays negative: (-1)<<4 is -16, out of range.
class ShiftLeftSignedUnsat;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == -1; pool[r<<4] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[240] = 8'h77;
  endfunction
endclass

// Narrow addition wraps before widening: 100+100 is -56, out of range.
class ByteAddWrapUnsat;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:400];
  constraint c { r1 == 100; r2 == 100; pool[r1+r2] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[200] = 8'h77;
  endfunction
endclass

// Same from below: (-100)+(-100) is 56, which reads element 56.
class ByteAddWrapSat;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:400];
  constraint c { r1 == -100; r2 == -100; pool[r1+r2] == 8'h77; }
  function new();
    pool[56] = 8'h77;
  endfunction
endclass

// The negation edge: -(-128) wraps to -128, out of range.
class NegateEdgeUnsat;
  rand byte r;
  bit [7:0] pool[5:270];
  constraint c { r == -128; pool[-r] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[128] = 8'h77;
  endfunction
endclass

// The division edge: (-128)/(-1) wraps to -128, out of range.
class DivEdgeUnsat;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:270];
  constraint c { r1 == -128; r2 == -1; pool[r1/r2] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[128] = 8'h77;
  endfunction
endclass

// A logical shift of an unsigned value is unambiguous: 250>>1 is 125.
class ShiftRightUnsBiasIndex;
  rand bit [7:0] u;
  bit [7:0] pool[5:270];
  constraint c { u == 250; pool[u>>1] == 8'hB0; }
  function new();
    pool[125] = 8'hB0;
  endfunction
endclass

// Same for full-width values: 252>>1 reads element 126.
class ShiftRightIntBiasIndex;
  rand int r;
  bit [7:0] pool[5:270];
  constraint c { r == 252; pool[r>>1] == 8'hB0; }
  function new();
    pool[126] = 8'hB0;
  endfunction
endclass

// An arithmetic shift of a signed value: 12>>>1 reads element 6.
class ShiftRSIntBiasIndex;
  rand int r;
  bit [7:0] pool[5:12];
  constraint c { r == 12; pool[r>>>1] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Same, but negative: (-4)>>>1 is -2, out of range.
class ShiftRSIntUnsat;
  rand int r;
  bit [7:0] pool[5:12];
  constraint c { r == -4; pool[r>>>1] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[6] = 8'h77;
  endfunction
endclass

// Comparisons keep their signedness below the bias.
class CondCompareBiasIndex;
  rand byte r1;
  rand byte r2;
  rand bit [7:0] u1;
  bit [7:0] pool[5:12];
  constraint c { r1 == -1; r2 == -2; u1 == 3; pool[((r1 > r2) == (u1 < 5)) ? 6 : 7] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
    pool[7] = 8'hB1;
  endfunction
endclass

// Same for the remaining comparison flavors.
class CondCompareBiasIndex2;
  rand byte r3;
  rand byte r4;
  rand bit [7:0] u2;
  bit [7:0] pool[5:12];
  constraint c { r3 == -1; r4 == -1; u2 == 255; pool[((r3 >= r4) != (u2 <= 250)) ? 6 : 7] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
    pool[7] = 8'hB1;
  endfunction
endclass

// Narrow arithmetic inside a comparison wraps too: (100*100)>5 holds.
class CondArithBiasIndex;
  rand byte r1;
  rand byte r2;
  rand byte r3;
  rand byte r4;
  bit [7:0] pool[5:12];
  constraint c {
    r1 == 100; r2 == 100; r3 == -12; r4 == -2;
    pool[(((r1*r2) > 5) == ((r3/r4) < 8)) ? 6 : 7] == 8'hB0;
  }
  function new();
    pool[6] = 8'hB0;
    pool[7] = 8'hB1;
  endfunction
endclass

// Same for the remainder: (-12)%5 is nonzero, so the else arm wins.
class CondModBiasIndex;
  rand byte r5;
  rand byte r6;
  bit [7:0] pool[5:12];
  constraint c { r5 == -12; r6 == 5; pool[((r5 % r6) == 0) ? 6 : 7] == 8'hB0; }
  function new();
    pool[6] = 8'hB1;
    pool[7] = 8'hB0;
  endfunction
endclass

// A concatenation feeding division stays unsigned throughout.
class ConcatDivBiasIndex;
  rand byte r23;
  rand byte r24;
  bit [7:0] pool[5:270];
  constraint c { r23 == -1; r24 == 16; pool[(({r23, 3'b0}) / 11'(r24))] == 8'hAB; }
  function new();
    pool[127] = 8'hAB;
  endfunction
endclass

// A nested select through a nonzero base signs its elements.
class NestedNonzeroSat;
  rand int r;
  byte inner2[5:12];
  bit [7:0] pool[5:270];
  constraint c { r == 7; pool[inner2[r]] == 8'hB0; }
  function new();
    inner2[7] = 8;
    pool[8] = 8'hB0;
  endfunction
endclass

// Same, but the element is negative: pool[-1] stays out of range.
class NestedNonzeroUnsat;
  rand int r;
  byte inner2[5:12];
  bit [7:0] pool[5:270];
  constraint c { r == 6; pool[inner2[r]] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    inner2[6] = -1;
    pool[255] = 8'h77;
  endfunction
endclass

// A part-select feeding addition keeps its own width.
class SelectArithBiasIndex;
  rand int u;
  bit [7:0] pool[5:12];
  constraint c { u == 0; pool[u[3:0]+6] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A negation feeding wider arithmetic: (-(-1))+6 reads element 7.
class NegateOperandBiasIndex;
  rand byte r;
  bit [7:0] pool[5:12];
  constraint c { r == -1; pool[(-r)+6] == 8'hB0; }
  function new();
    pool[7] = 8'hB0;
  endfunction
endclass

// Full-width addition needs no widening: (-1)+6 reads element 5.
class IntAddBiasIndex;
  rand int r;
  bit [7:0] pool[5:12];
  constraint c { r == -1; pool[r+6] == 8'hB0; }
  function new();
    pool[5] = 8'hB0;
  endfunction
endclass

// The remainder below the bias is signed: (-12)%5 is -2, out of range.
class ModBiasIndexUnsat;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[1:12];
  constraint c { r1 == -12; r2 == 5; pool[r1%r2] == 8'h77; }
  function new();
    foreach (pool[i]) pool[i] = 8'h11;
    pool[4] = 8'h77;
  endfunction
endclass

// Every operator kind feeding a division context, each on its own slot.
class DivOperandKinds;
  rand byte r1; rand byte r2; rand byte r3; rand byte r4;
  rand byte r5; rand byte r6; rand bit [7:0] u1; rand byte r7;
  rand int i1; rand byte r8; rand byte r9; rand byte r10; rand byte r11;
  rand byte r12; rand byte r13; rand byte r14; rand byte r15; rand byte r16;
  rand byte r17; rand byte r18; rand byte r19; rand byte r20; rand byte r21;
  rand byte r22; rand byte r23; rand byte r24; rand byte r25; rand byte r26;
  rand byte r27; rand byte r28;
  bit [7:0] pool[5:270];
  function new();
    pool[9] = 8'hA1; pool[10] = 8'hA2; pool[11] = 8'hA3; pool[34] = 8'hA4;
    pool[13] = 8'hA5; pool[21] = 8'hA6; pool[15] = 8'hA7; pool[17] = 8'hA8;
    pool[7] = 8'hA9; pool[6] = 8'hAA; pool[127] = 8'hAB; pool[5] = 8'hAC;
  endfunction
  constraint c {
    r1 == -7; r2 == 2; r3 == -6; r4 == 2; r5 == 3; r6 == 2;
    u1 == 250; r7 == 5; i1 == 12; r8 == 2; r9 == 10; r10 == 10; r11 == 2;
    r12 == 2; r13 == 3; r14 == 2; r15 == -12; r16 == 2; r17 == 2;
    r18 == 17; r19 == 5; r20 == 2; r21 == -1; r22 == 0; r23 == -1; r24 == 16;
    r25 == -1; r26 == 0; r27 == -1; r28 == 1;
    pool[((~r1)/r2)+6] == 8'hA1;
    pool[((-r3)/r4)+7] == 8'hA2;
    pool[(((r5<<1)/r6))+8] == 8'hA3;
    pool[(((u1>>1)/r7))+9] == 8'hA4;
    pool[(((i1>>>1)/int'(r8)))+10] == 8'hA5;
    pool[(((r9+r10)/r11))+11] == 8'hA6;
    pool[(((r12*r13)/r14))+12] == 8'hA7;
    pool[(((r15/r16)/r17))+20] == 8'hA8;
    pool[(((r18%r19)/r20))+6] == 8'hA9;
    pool[(((r21>r22)+6)/1)] == 8'hAA;
    pool[(({r23,3'b0})/11'(r24))] == 8'hAB;
    pool[((((r25>0)?r26:r27)/r28))+6] == 8'hAC;
  }
endclass

// Mixed signs divide unsigned: 0xFF/2 is 127, which reads element 127.
class MixedDivBiasIndex;
  rand byte r;
  rand bit [7:0] u;
  bit [7:0] pool[5:270];
  constraint c { r == -1; u == 2; pool[r/u] == 8'hB0; }
  function new();
    pool[127] = 8'hB0;
  endfunction
endclass

// A reduction feeding wider arithmetic stays narrow: (&0xFF)+6 reads element 7.
class RedAndOperandBiasIndex;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:12];
  constraint c { r1 == -1; r2 == 0; pool[((&(r1+r2))+6)] == 8'hB0; }
  function new();
    pool[7] = 8'hB0;
  endfunction
endclass

// An unsigned ordering stays unsigned: (200>=100)+5 reads element 6.
class UnsignedGteBiasIndex;
  rand byte unsigned u3;
  rand byte unsigned u4;
  bit [7:0] pool[5:12];
  constraint c { u3 == 200; u4 == 100; pool[((u3>=u4)+5)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A signed ordering keeps its sign: (-3<=5)+5 reads element 6.
class SignedLteBiasIndex;
  rand byte r5;
  rand byte r6;
  bit [7:0] pool[5:12];
  constraint c { r5 == -3; r6 == 5; pool[((r5<=r6)+5)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// An equality feeding arithmetic stays one bit: (3==3)+5 reads element 6.
class EqOperandBiasIndex;
  rand byte r1;
  rand byte r2;
  bit [7:0] pool[5:12];
  constraint c { r1 == 3; r2 == 3; pool[((r1==r2)+5)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A sum feeding division divides before widening: (20+4)/6+2 reads element 6.
class AddDivBiasIndex;
  rand byte r1;
  rand byte r2;
  rand byte r3;
  bit [7:0] pool[5:12];
  constraint c { r1 == 20; r2 == 4; r3 == 6; pool[(((r1+r2)/r3)+2)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A sum feeding a comparison compares narrow: (20+4)>10 selects element 7.
class AddGtBiasIndex;
  rand byte r1;
  rand byte r2;
  rand byte r3;
  bit [7:0] pool[5:12];
  constraint c { r1 == 20; r2 == 4; r3 == 10; pool[(((r1+r2)>r3)+6)] == 8'hB0; }
  function new();
    pool[7] = 8'hB0;
  endfunction
endclass

// Mixed signs divide wide: (-10+250)/5-42 reads element 6.
class MixedAddDivBiasIndex;
  rand byte s8;
  rand byte unsigned u8;
  bit [7:0] pool[5:12];
  constraint c { s8 == -10; u8 == 250; pool[(((32'(s8)+32'(u8))/5)-42)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A mixed sum keeps all 32 bits: (100+200)-294 reads element 6.
class MixedAddWideBiasIndex;
  rand byte s8;
  rand byte unsigned u8;
  bit [7:0] pool[5:12];
  constraint c { s8 == 100; u8 == 200; pool[((32'(s8)+32'(u8))-294)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// An unsigned sum keeps its high bit: (200+55)-249 reads element 6.
class UnsignedAddHighBiasIndex;
  rand byte unsigned u1;
  rand byte unsigned u2;
  bit [7:0] pool[5:12];
  constraint c { u1 == 200; u2 == 55; pool[((32'(u1)+32'(u2))-249)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// An unsigned choice divides narrow: (flag?20:4)/6+3 reads element 6.
class CondDivUnsignedBiasIndex;
  rand bit flag;
  rand byte unsigned u1;
  rand byte unsigned u2;
  rand byte x;
  bit [7:0] pool[5:12];
  constraint c { flag == 1; u1 == 20; u2 == 4; x == 6;
                 pool[((((flag?u1:u2)/x))+3)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A mixed choice divides wide: (flag?20:4)/6+3 reads element 6.
class CondDivMixedBiasIndex;
  rand bit flag;
  rand byte s1;
  rand byte unsigned u2;
  rand byte x;
  bit [7:0] pool[5:12];
  constraint c { flag == 1; s1 == 20; u2 == 4; x == 6;
                 pool[((((flag?s1:u2)/x))+3)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// A narrow else-arm widens with its sign: flag picks element 7.
class CondSignedNarrowElseBiasIndex;
  rand bit flag;
  rand byte r8;
  bit [7:0] pool[5:12];
  constraint c { flag == 0; r8 == 7; pool[(flag?32'd6:32'(r8))] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
    pool[7] = 8'hB0;
  endfunction
endclass

// An unsigned remainder stays unsigned: (20%6)+4 reads element 6.
class UnsignedModBiasIndex;
  rand byte unsigned u1;
  rand byte unsigned u2;
  bit [7:0] pool[5:12];
  constraint c { u1 == 20; u2 == 6; pool[(((u1%u2))+4)] == 8'hB0; }
  function new();
    pool[6] = 8'hB0;
  endfunction
endclass

// Mixed signs compare unsigned: 255>255 is false, so the else arm wins.
class MixedCmpBiasIndex;
  rand byte r;
  rand bit [7:0] u;
  bit [7:0] pool[5:12];
  constraint c { r == -1; u == 255; pool[(r > u) ? 6 : 7] == 8'hB0; }
  function new();
    pool[6] = 8'hB1;
    pool[7] = 8'hB0;
  endfunction
endclass

// A rand index into a fixed array reached through a rand dynamic, queue,
// or associative outer array.
class RandDynOuterRandIndex;
  rand int idx;
  rand bit [7:0] data[][2];
  constraint c { idx inside {[0:1]}; data.size() == 1; data[0][idx] == 8'hAA; }
endclass

class RandQueueOuterRandIndex;
  rand int idx;
  rand bit [7:0] data[$][2];
  constraint c { idx inside {[0:1]}; data.size() == 1; data[0][idx] == 8'hAA; }
endclass

class RandAssocOuterRandIndex;
  rand int idx;
  rand bit [7:0] data[int][2];
  constraint c { idx inside {[0:1]}; data[0][idx] == 8'hAA; }
  function new();
    data[0][0] = 8'h00;
    data[0][1] = 8'h00;
  endfunction
endclass

// A non-rand index (a method call) on the way to a non-rand array.
class HolderQueueLastIndex;
  rand int idx;
  Holder holders[$];
  constraint c { idx inside {[0:15]}; holders[holders.size() - 1].used[idx]; }
  function new();
    Holder h0 = new;
    Holder h1 = new;
    h1.used[5] = 1'b1;
    holders.push_back(h0);
    holders.push_back(h1);
  endfunction
endclass

typedef struct {
  bit [7:0] a;
  bit [7:0] b;
} s_t;

// Member select off a constant-indexed struct array, which must keep dotted
// member naming rather than folding to a generic select.
class StructArrayConstIndex;
  rand s_t arr[4];
  constraint c_a { arr[2].a == 8'hBB; }
endclass

// Packed-struct elements are ordinary bit vectors.
typedef struct packed {
  bit [1:0] x;
  bit y;
} packed_elem_t;
class PackedStructPool;
  rand int idx;
  packed_elem_t used[4];
  constraint c { idx inside {[0:5]}; used[idx] == 3'b101; }
  function new();
    used = '{3'b000, 3'b001, 3'b101, 3'b010};
  endfunction
endclass

// The array as a member of a non-rand struct, in range and out of range.
typedef struct {
  bit used[4];
} pool_s;
class StructFieldPool;
  rand int idx;
  pool_s pool;
  constraint c { idx inside {[0:5]}; pool.used[idx] == 0; idx != 4; idx != 5; }
  function new();
    pool.used = '{1, 1, 0, 1};
  endfunction
endclass

class StructFieldPoolOob;
  rand int idx;
  pool_s pool;
  constraint c { idx == 6; pool.used[idx] == 0; }
  function new();
    pool.used = '{1, 1, 1, 1};
  endfunction
endclass

// A member index to std::randomize(): the answer (2) needs the index's high
// bit, which a truncation to the array's index width would lose.
class StdMemberPool;
  int idx;
  bit [7:0] used[4];
  function new();
    used = '{8'h11, 8'h22, 8'h33, 8'h44};
  endfunction
endclass

// An explicit size cast does truncate, so 4 reads element 0.
class ExplicitlyCastIndex;
  rand int unsigned idx;
  bit used[4] = '{1, 1, 1, 1};
  constraint c { idx == 4; used[2'(idx)] == 0; }
endclass

// A negative signed index is out of range, so the read is the default.
class SignedNegativeIndex;
  rand bit signed [1:0] idx;
  bit used[3] = '{1, 1, 1};
  constraint c { idx == -2; used[idx] == 0; }
endclass

// Same, into an array whose range doesn't start at 0
class SignedNegativeIndexBase1;
  rand bit signed [1:0] idx;
  bit used[1:3] = '{1, 1, 1};
  constraint c { used[idx] == 0; }
endclass

// An unsigned index into the same kind of range
class UnsignedIndexBase1;
  rand bit [1:0] idx;
  bit used[1:3] = '{1, 0, 1};
  constraint c { used[idx] == 0; }
endclass

// A range below 0, which offsets the index by adding rather than subtracting
class NegativeBaseIndex;
  rand int idx;
  bit used[-1:1] = '{1, 0, 1};
  constraint c { idx inside {[-3:3]}; used[idx] == 0; idx > -2; idx < 2; }
endclass

// An index narrower than the array's index width still reaches every element.
/* verilator lint_off WIDTHEXPAND */
class NarrowIndex;
  rand bit idx;
  bit used[4] = '{1, 0, 1, 1};
  constraint c { used[idx] == 0; }
endclass
/* verilator lint_on WIDTHEXPAND */


module t;
  initial begin
    UniqueIdPool obj;
    UniqueIdPoolViaMember mobj;
    UniqueIdPoolNonZeroBase nzobj;
    UniqueIdPoolDescBase descobj;
    RandArrayRandIndex rand_obj;
    RandMultidimRandIndex mrand_obj;
    RandMultidimRandIndexOuter mrand_outer_obj;
    RandMultidimRandIndexOuterMinimal mrand_outer_min_obj;
    RandMultidimRandIndexDeep mrand_deep_obj;
    RandQueueRandIndex rq_obj;
    StructArrayConstIndex sa_const_obj;
    OutOfBoundsIndex oob_obj;
    OutOfBoundsIndexNegative oob_neg_obj;
    OutOfBoundsIndexNonZeroBase oob_nzb_obj;
    ExplicitlyCastIndex cast_obj;
    SignedNegativeIndex sneg_obj;
    SignedNegativeIndexBase1 sneg1_obj;
    UnsignedIndexBase1 ubase1_obj;
    NegativeBaseIndex negbase_obj;
    NarrowIndex narrow_obj;
    OutOfBoundsIndexPastIndexWidth oob_wide_obj;
    ExplicitlyTruncatedIndex trunc_obj;
    ExactWidthIndex exact_obj;
    InlineWithPool iw_obj;
    CompoundBiasIndex cb_obj;
    CompoundBiasIndexUnsat cb_u_obj;
    NegateBiasIndex neg_obj;
    BitwiseNotBiasIndex not_obj;
    MultBiasIndex mul_obj;
    MultBiasIndexUnsat mul_u_obj;
    DivBiasIndex div_obj;
    DivBiasIndexUnsat div_u_obj;
    IntDivBiasIndex idiv_obj;
    UnsDivBiasIndex udiv_obj;
    ShiftLeftWrapUnsat shlw_u_obj;
    ShiftLeftBiasIndex shl_obj;
    ShiftLeftSignedUnsat shls_u_obj;
    ByteAddWrapUnsat baw_u_obj;
    ByteAddWrapSat baw_obj;
    NegateEdgeUnsat nege_u_obj;
    DivEdgeUnsat dive_u_obj;
    ShiftRightUnsBiasIndex shru_obj;
    ShiftRightIntBiasIndex shri_obj;
    ShiftRSIntBiasIndex shrs_obj;
    ShiftRSIntUnsat shrs_u_obj;
    CondCompareBiasIndex cc_obj;
    CondCompareBiasIndex2 cc2_obj;
    CondArithBiasIndex ca_obj;
    CondModBiasIndex cm_obj;
    ConcatDivBiasIndex cd_obj;
    NestedNonzeroSat nn_obj;
    NestedNonzeroUnsat nn_u_obj;
    SelectArithBiasIndex sa_obj;
    NegateOperandBiasIndex no_obj;
    IntAddBiasIndex ia_obj;
    ModBiasIndexUnsat mod_u_obj;
    DivOperandKinds dok_obj;
    MixedDivBiasIndex md_obj;
    MixedCmpBiasIndex mc_obj;
    RedAndOperandBiasIndex rao_obj;
    UnsignedGteBiasIndex ugte_obj;
    SignedLteBiasIndex slte_obj;
    EqOperandBiasIndex eqop_obj;
    AddDivBiasIndex adddiv_obj;
    AddGtBiasIndex addgt_obj;
    MixedAddDivBiasIndex madd_obj;
    MixedAddWideBiasIndex maw_obj;
    UnsignedAddHighBiasIndex uah_obj;
    CondDivUnsignedBiasIndex cdu_obj;
    CondDivMixedBiasIndex cdm_obj;
    CondSignedNarrowElseBiasIndex csne_obj;
    UnsignedModBiasIndex umod_obj;
    RandDynOuterRandIndex rdyn_outer_obj;
    RandQueueOuterRandIndex rq_outer_obj;
    RandAssocOuterRandIndex raa_outer_obj;
    HolderQueueLastIndex hq_last_obj;
    PackedStructPool ps_obj;
    StructFieldPool sf_obj;
    StructFieldPoolOob sf_oob_obj;
    bit [15:0] seen;
    int randomize_result;

    nzobj = new;
    seen = '0;
    for (int i = 0; i < 16; i++) begin
      randomize_result = nzobj.randomize();
      `checkd(randomize_result, 1);
      if (nzobj.id < 1 || nzobj.id > 16) begin
        $write("%%Error: id out of range: %0d\n", nzobj.id);
        `stop;
      end
      if (seen[nzobj.id - 1]) begin
        $write("%%Error: id %0d drawn twice\n", nzobj.id);
        `stop;
      end
      seen[nzobj.id - 1] = 1'b1;
      nzobj.used[nzobj.id] = 1'b1;
    end
    `checkd(seen, 16'hffff);
    randomize_result = nzobj.randomize();
    `checkd(randomize_result, 0);

    descobj = new;
    seen = '0;
    for (int i = 0; i < 16; i++) begin
      randomize_result = descobj.randomize();
      `checkd(randomize_result, 1);
      if (descobj.id < 1 || descobj.id > 16) begin
        $write("%%Error: id out of range: %0d\n", descobj.id);
        `stop;
      end
      if (seen[descobj.id - 1]) begin
        $write("%%Error: id %0d drawn twice\n", descobj.id);
        `stop;
      end
      seen[descobj.id - 1] = 1'b1;
      descobj.used[descobj.id] = 1'b1;
    end
    `checkd(seen, 16'hffff);
    randomize_result = descobj.randomize();
    `checkd(randomize_result, 0);

    rand_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rand_obj.data[rand_obj.idx], 8'hAA);
    end

    mrand_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_obj.data[mrand_obj.idx][0], 8'hAA);
    end

    mrand_outer_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_outer_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_outer_obj.data[0][mrand_outer_obj.idx], 8'hAA);
    end

    mrand_outer_min_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_outer_min_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_outer_min_obj.data[0][mrand_outer_min_obj.idx], 8'hAA);
    end

    mrand_deep_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = mrand_deep_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(mrand_deep_obj.data[1][2][mrand_deep_obj.idx], 8'hAA);
    end

    rq_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rq_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rq_obj.data[rq_obj.idx], 1'b1);
    end

    sa_const_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = sa_const_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(sa_const_obj.arr[2].a, 8'hBB);
    end

    oob_obj = new;
    randomize_result = oob_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(oob_obj.idx, 3);

    oob_neg_obj = new;
    randomize_result = oob_neg_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(oob_neg_obj.idx, -1);

    oob_nzb_obj = new;
    randomize_result = oob_nzb_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(oob_nzb_obj.idx, 4);

    cast_obj = new;
    randomize_result = cast_obj.randomize();
    `checkd(randomize_result, 0);

    sneg_obj = new;
    randomize_result = sneg_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(sneg_obj.idx, -2);

    sneg1_obj = new;
    for (int i = 0; i < 10; i++) begin
      randomize_result = sneg1_obj.randomize();
      `checkd(randomize_result, 1);
      if (sneg1_obj.idx > 0) `stop;
    end

    ubase1_obj = new;
    randomize_result = ubase1_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(ubase1_obj.idx, 2);

    negbase_obj = new;
    for (int i = 0; i < 10; i++) begin
      randomize_result = negbase_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(negbase_obj.idx, 0);
    end

    narrow_obj = new;
    for (int i = 0; i < 10; i++) begin
      randomize_result = narrow_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(narrow_obj.idx, 1);
    end

    oob_wide_obj = new;
    seen = '0;
    for (int i = 0; i < 20; i++) begin
      randomize_result = oob_wide_obj.randomize();
      `checkd(randomize_result, 1);
      if (oob_wide_obj.idx < 4 || oob_wide_obj.idx > 5) begin
        $write("%%Error: idx out of range: %0d\n", oob_wide_obj.idx);
        `stop;
      end
      seen[oob_wide_obj.idx] = 1'b1;
    end
    `checkd(seen, 16'h0030);

    trunc_obj = new;
    randomize_result = trunc_obj.randomize();
    `checkd(randomize_result, 0);

    exact_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = exact_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(exact_obj.idx, 2);
    end

    rdyn_outer_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rdyn_outer_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rdyn_outer_obj.data[0][rdyn_outer_obj.idx], 8'hAA);
    end

    rq_outer_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = rq_outer_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(rq_outer_obj.data[0][rq_outer_obj.idx], 8'hAA);
    end

    raa_outer_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = raa_outer_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(raa_outer_obj.data[0][raa_outer_obj.idx], 8'hAA);
    end

    hq_last_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = hq_last_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(hq_last_obj.idx, 5);
    end

    ps_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = ps_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(ps_obj.idx, 2);
    end

    sf_obj = new;
    for (int i = 0; i < 20; i++) begin
      randomize_result = sf_obj.randomize();
      `checkd(randomize_result, 1);
      `checkd(sf_obj.idx, 2);
    end

    sf_oob_obj = new;
    randomize_result = sf_oob_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(sf_oob_obj.idx, 6);

    mobj = new;
    for (int i = 0; i < 16; i++) begin
      randomize_result = mobj.randomize();
      `checkd(randomize_result, 1);
      if (mobj.id < 0 || mobj.id > 15) begin
        $write("%%Error: id out of range: %0d\n", mobj.id);
        `stop;
      end
      mobj.holder.used[mobj.id] = 1'b1;
    end

    // Repeat the whole draw-all-then-exhaust cycle on a fresh object each
    // time, to guard against solver-randomness flakiness masking a bug.
    repeat (20) begin
      obj = new;
      seen = '0;
      for (int i = 0; i < 16; i++) begin
        randomize_result = obj.randomize();
        `checkd(randomize_result, 1);
        // Each draw must be a legal, not-yet-drawn value
        if (obj.id < 0 || obj.id > 15) begin
          $write("%%Error: id out of range: %0d\n", obj.id);
          `stop;
        end
        if (seen[obj.id]) begin
          $write("%%Error: id %0d drawn twice\n", obj.id);
          `stop;
        end
        seen[obj.id] = 1'b1;
        obj.used[obj.id] = 1'b1;
      end
      // All 16 ids must have been drawn exactly once
      `checkd(seen, 16'hffff);
      // Pool exhausted -- no legal value remains
      randomize_result = obj.randomize();
      `checkd(randomize_result, 0);
    end

    // A rand index into an array that's itself a std::randomize() argument:
    // the argument's own captured copy must stay a symbolic SMT value, the
    // same as a class's own rand member would.
    begin
      bit [7:0] sarr[4];
      int sidx;
      int std_result;
      for (int i = 0; i < 20; i++) begin
        sarr = '{0, 0, 0, 0};
        std_result = std::randomize(sarr, sidx) with {sidx inside {[0 : 3]}; sarr[sidx] == 8'hFF;};
        `checkd(std_result, 1);
        `checkd(sarr[sidx], 8'hFF);
      end
    end

    // Same rand index, but also reaching a plain non-rand array in the same
    // expression -- that side must still get the non-rand elementwise treatment,
    // not be mistaken for part of the std::randomize() call's own rand set.
    begin
      bit [7:0] sarr2[4];
      bit [7:0] other[4];
      int sidx2;
      int std_result2;
      other = '{8'h11, 8'h22, 8'h33, 8'h44};
      for (int i = 0; i < 20; i++) begin
        sarr2 = '{0, 0, 0, 0};
        std_result2 = std::randomize(
            sarr2, sidx2) with {sidx2 inside {[0 : 3]}; sarr2[sidx2] == other[sidx2];};
        `checkd(std_result2, 1);
        `checkd(sarr2[sidx2], other[sidx2]);
      end
    end

    begin
      StdMemberPool mobj;
      int std_result3;
      mobj = new;
      for (int i = 0; i < 20; i++) begin
        mobj.idx = 0;
        std_result3 = std::randomize(
            mobj.idx) with {mobj.idx inside {[0 : 3]}; mobj.used[mobj.idx] == 8'h33;};
        `checkd(std_result3, 1);
        `checkd(mobj.idx, 2);
        `checkd(mobj.used[mobj.idx], 8'h33);
      end
    end

    // Bare and this-qualified spellings of the with-clause member index.
    iw_obj = new;
    randomize_result = iw_obj.randomize() with { idx inside {[0:3]}; pool[idx] == 8'h33; };
    `checkd(randomize_result, 1);
    `checkd(iw_obj.idx, 2);
    randomize_result = iw_obj.randomize() with { idx inside {[0:3]}; pool[idx] == 8'h00; };
    `checkd(randomize_result, 0);
    randomize_result = iw_obj.randomize() with { idx inside {[0:3]}; pool[this.idx] == 8'h00; };
    `checkd(randomize_result, 0);

    cb_obj = new;
    randomize_result = cb_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cb_obj.r, -1);

    cb_u_obj = new;
    randomize_result = cb_u_obj.randomize();
    `checkd(randomize_result, 0);

    neg_obj = new;
    randomize_result = neg_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(neg_obj.r, -6);

    not_obj = new;
    randomize_result = not_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(not_obj.r, -7);

    mul_obj = new;
    randomize_result = mul_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(mul_obj.r1, -2);

    mul_u_obj = new;
    randomize_result = mul_u_obj.randomize();
    `checkd(randomize_result, 0);

    div_obj = new;
    randomize_result = div_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(div_obj.r1, -12);

    div_u_obj = new;
    randomize_result = div_u_obj.randomize();
    `checkd(randomize_result, 0);

    idiv_obj = new;
    randomize_result = idiv_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(idiv_obj.r1, -12);

    udiv_obj = new;
    randomize_result = udiv_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(udiv_obj.u1, 12);

    shlw_u_obj = new;
    randomize_result = shlw_u_obj.randomize();
    `checkd(randomize_result, 0);

    shl_obj = new;
    randomize_result = shl_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(shl_obj.r, 1);

    shls_u_obj = new;
    randomize_result = shls_u_obj.randomize();
    `checkd(randomize_result, 0);

    baw_u_obj = new;
    randomize_result = baw_u_obj.randomize();
    `checkd(randomize_result, 0);

    baw_obj = new;
    randomize_result = baw_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(baw_obj.r1, -100);

    nege_u_obj = new;
    randomize_result = nege_u_obj.randomize();
    `checkd(randomize_result, 0);

    dive_u_obj = new;
    randomize_result = dive_u_obj.randomize();
    `checkd(randomize_result, 0);

    shru_obj = new;
    randomize_result = shru_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(shru_obj.u, 250);

    shri_obj = new;
    randomize_result = shri_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(shri_obj.r, 252);

    shrs_obj = new;
    randomize_result = shrs_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(shrs_obj.r, 12);

    shrs_u_obj = new;
    randomize_result = shrs_u_obj.randomize();
    `checkd(randomize_result, 0);

    cc_obj = new;
    randomize_result = cc_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cc_obj.r1, -1);

    cc2_obj = new;
    randomize_result = cc2_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cc2_obj.r3, -1);

    ca_obj = new;
    randomize_result = ca_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(ca_obj.r1, 100);

    cm_obj = new;
    randomize_result = cm_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cm_obj.r5, -12);

    cd_obj = new;
    randomize_result = cd_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cd_obj.r23, -1);

    nn_obj = new;
    randomize_result = nn_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(nn_obj.r, 7);

    nn_u_obj = new;
    randomize_result = nn_u_obj.randomize();
    `checkd(randomize_result, 0);

    sa_obj = new;
    randomize_result = sa_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(sa_obj.u, 0);

    no_obj = new;
    randomize_result = no_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(no_obj.r, -1);

    ia_obj = new;
    randomize_result = ia_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(ia_obj.r, -1);

    mod_u_obj = new;
    randomize_result = mod_u_obj.randomize();
    `checkd(randomize_result, 0);

    dok_obj = new;
    randomize_result = dok_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(dok_obj.r1, -7);

    md_obj = new;
    randomize_result = md_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(md_obj.r, -1);

    mc_obj = new;
    randomize_result = mc_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(mc_obj.r, -1);

    rao_obj = new;
    randomize_result = rao_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(rao_obj.r1, -1);

    ugte_obj = new;
    randomize_result = ugte_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(ugte_obj.u3, 200);

    slte_obj = new;
    randomize_result = slte_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(slte_obj.r5, -3);

    eqop_obj = new;
    randomize_result = eqop_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(eqop_obj.r1, 3);

    adddiv_obj = new;
    randomize_result = adddiv_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(adddiv_obj.r1, 20);

    addgt_obj = new;
    randomize_result = addgt_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(addgt_obj.r1, 20);

    madd_obj = new;
    randomize_result = madd_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(madd_obj.s8, -10);

    maw_obj = new;
    randomize_result = maw_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(maw_obj.s8, 100);

    uah_obj = new;
    randomize_result = uah_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(uah_obj.u1, 200);

    cdu_obj = new;
    randomize_result = cdu_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cdu_obj.u1, 20);

    cdm_obj = new;
    randomize_result = cdm_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(cdm_obj.s1, 20);

    csne_obj = new;
    randomize_result = csne_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(csne_obj.r8, 7);

    umod_obj = new;
    randomize_result = umod_obj.randomize();
    `checkd(randomize_result, 1);
    `checkd(umod_obj.u1, 20);

    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
