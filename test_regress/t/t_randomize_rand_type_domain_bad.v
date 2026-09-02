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

module t;
  initial begin
    CHandle obj1;
    CReal obj2;
    CChandle obj3;
    CString obj4;
    CEvent obj5;
    obj1 = new;
    obj2 = new;
    obj3 = new;
    obj4 = new;
    obj5 = new;
    if (obj1.randomize() == 0) $stop;
    if (obj2.randomize() == 0) $stop;
    if (obj3.randomize() == 0) $stop;
    if (obj4.randomize() == 0) $stop;
    if (obj5.randomize() == 0) $stop;
  end
endmodule
