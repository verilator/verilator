// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// IEEE 1800-2023 18.4 type-eligibility rules for rand/randc: each class
// below is illegal on its own for a distinct reason, not a working design.

class Item;
  rand int val;
endclass

// randc on an object handle: "Object handles shall not be declared randc."
class CHandle;
  randc Item h;
endclass

// randc on a real variable: "Real variables shall not be declared randc."
class CReal;
  randc real v;
endclass

// chandle is not in the rand-eligible type domain at all.
class CChandle;
  rand chandle h;
endclass

// string is not in the rand-eligible type domain.
class CString;
  rand string s;
endclass

// event is not in the rand-eligible type domain.
class CEvent;
  rand event e;
endclass

// randc on realtime: same LRM rule as real, checked separately since
// realtime isn't literally the same dtype kind as real.
class CRealtime;
  randc realtime rt;
endclass

// A virtual interface handle is not in 18.4's enumerated domain either.
interface Bus;
endinterface
class CVif;
  rand virtual Bus vif;
endclass

// A typedef'd queue of an ineligible type: proves the dtype-unwrap walk
// skips refs at every recursion level, not just the outermost one.
typedef chandle chandle_q_t[$];
class CChandleQueue;
  rand chandle_q_t q;
endclass

module t;
  initial begin
    CHandle obj1;
    CReal obj2;
    CChandle obj3;
    CString obj4;
    CEvent obj5;
    CRealtime obj6;
    CVif obj7;
    CChandleQueue obj8;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    obj6 = new;
    obj7 = new;
    obj8 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
    if (obj6.randomize() == 0) $stop;
    if (obj7.randomize() == 0) $stop;
    if (obj8.randomize() == 0) $stop;
  end
endmodule
