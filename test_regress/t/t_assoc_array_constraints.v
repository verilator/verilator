// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define check_rand(cl, field, cond) \
begin \
   automatic longint prev_result; \
   automatic int ok; \
   if (!bit'(cl.randomize())) `stop; \
   prev_result = longint'(field); \
   if (!(cond)) `stop; \
   repeat(20) begin \
      longint result; \
      if (!bit'(cl.randomize())) `stop; \
      result = longint'(field); \
      if (!(cond)) `stop; \
      if (result != prev_result) ok = 1; \
      prev_result = result; \
   end \
   if (ok != 1) `stop; \
end
// verilog_format: on

class Empty;
  rand int x;
endclass

typedef struct packed {
  bit [3:0] hi;
  bit [3:0] lo;
} PackedStructKey;

typedef union packed {
  bit [7:0] k8;
  bit [7:0] k8b;
} PackedUnionKey;

typedef enum {
  EnumA,
  EnumB
} EnumKey;

class ClsNe;
  rand Empty empties[string];
  constraint c {empties["abc"] != empties["xyz"];}
endclass

class ClsEq;
  rand Empty empties[string];
  constraint c {empties["abc"] == empties["xyz"];}
endclass

class ClsNeK;
  rand Empty empties[string];
  constraint c {empties["abc"] != empties["abc"];}
endclass

class ClsEqK;
  rand Empty empties[string];
  constraint c {empties["abc"] == empties["abc"];}
endclass

class ClsMixed;
  rand int y;
  rand Empty empties[string];
  constraint c {
    y > 5;
    empties["abc"] != empties["xyz"];
  }
endclass

class ClsStructKey;
  rand Empty empties[PackedStructKey];
  PackedStructKey k1;
  PackedStructKey k2;
  constraint c {empties[k1] != empties[k2];}
endclass

class ClsUnionKey;
  rand Empty empties[PackedUnionKey];
  PackedUnionKey k1;
  PackedUnionKey k2;
  constraint c {empties[k1] != empties[k2];}
endclass

class ClsIntKey;
  rand Empty empties[int];
  constraint c {empties[1] != empties[2];}
endclass

class ClsEnumKey;
  rand Empty empties[EnumKey];
  constraint c {empties[EnumA] != empties[EnumB];}
endclass

class ClsStringKey;
  rand Empty empties[string];
  string k1;
  string k2;
  constraint c {empties[k1] != empties[k2];}
endclass

class ClsIntMember;
  rand Empty empties[int];
  function new();
    empties[5] = new;
  endfunction
  constraint c {empties[5].x > 0;}
endclass

class ClsByteMember;
  rand Empty empties[byte];
  function new();
    empties[8'h12] = new;
  endfunction
  constraint c {empties[8'h12].x > 0;}
endclass

class ClsStringMember;
  rand Empty empties[string];
  function new();
    empties["abc"] = new;
  endfunction
  constraint c {empties["abc"].x > 0;}
endclass

class ClsStringExprKey;
  rand Empty empties[string];
  string keys[2] = '{"abc", "xyz"};
  function new();
    empties["abc"] = new;
    empties["xyz"] = new;
  endfunction
  constraint c {
    empties[keys[0]] != empties[keys[1]];
    empties[keys[1]].x > 0;
  }
endclass

class KeyHolder;
  string name = "abc";
endclass

class ClsIntArrExprKey;
  rand int vals[string];
  string keys[2] = '{"abc", "xyz"};
  KeyHolder holder = new;
  function new();
    vals["abc"] = 0;
    vals["xyz"] = 0;
  endfunction
  constraint c {
    vals[keys[1]] > 5;
    vals[holder.name] > 7;
  }
endclass

class EmptyArrayHolder;
  rand Empty empties[string];
  function new();
    empties["abc"] = new;
  endfunction
endclass

class ClsNestedMember;
  rand EmptyArrayHolder holder;
  function new();
    holder = new;
  endfunction
  constraint c {holder.empties["abc"].x > 0;}
endclass

class ClsIntArr;
  rand int vals[string];
  function new();
    vals["abc"] = 0;
  endfunction
  constraint c {vals["abc"] > 0;}
endclass

class ClsState;
  Empty empties[string];
  constraint c {empties["abc"] != empties["xyz"];}
endclass

class NoState;
endclass

module t;
  initial begin
    automatic int ok;
    begin
      automatic ClsNe cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      `check_rand(cls, cls.empties["abc"].x, cls.empties["abc"] != cls.empties["xyz"]);
    end
    repeat (20) begin
      automatic ClsNe cls = new;
      automatic Empty e = new;
      cls.empties["abc"] = e;
      cls.empties["xyz"] = e;
      ok = cls.randomize();
      `checkd(ok, 0);
    end
    begin
      automatic ClsEq cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      ok = cls.randomize();
      `checkd(ok, 0);
    end
    begin
      automatic ClsEq cls = new;
      automatic Empty e = new;
      cls.empties["abc"] = e;
      cls.empties["xyz"] = e;
      `check_rand(cls, e.x, cls.empties["abc"] == cls.empties["xyz"]);
    end
    begin
      automatic ClsNeK cls = new;
      cls.empties["abc"] = new;
      ok = cls.randomize();
      `checkd(ok, 0);
    end
    begin
      automatic ClsEqK cls = new;
      cls.empties["abc"] = new;
      `check_rand(cls, cls.empties["abc"].x, 1);
    end
    begin
      automatic ClsNe cls = new;
      ok = cls.randomize();
      `checkd(ok, 0);
      `checkd(cls.empties.size(), 0);
    end
    begin
      automatic ClsNe cls = new;
      cls.empties["abc"] = new;
      `check_rand(cls, cls.empties["abc"].x, cls.empties.size() == 1);
    end
    begin
      automatic ClsMixed cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      `check_rand(cls, cls.y, cls.y > 5 && cls.empties["abc"] != cls.empties["xyz"]);
    end
    begin
      automatic ClsStructKey cls = new;
      cls.k1 = 8'h12;
      cls.k2 = 8'h34;
      cls.empties[8'h12] = new;
      cls.empties[8'h34] = new;
      `check_rand(cls, cls.empties[8'h12].x, cls.empties[8'h12] != cls.empties[8'h34]);
    end
    begin
      automatic ClsUnionKey cls = new;
      cls.k1 = 8'h12;
      cls.k2 = 8'h34;
      cls.empties[8'h12] = new;
      cls.empties[8'h34] = new;
      `check_rand(cls, cls.empties[8'h12].x, cls.empties[8'h12] != cls.empties[8'h34]);
    end
    begin
      automatic ClsIntKey cls = new;
      cls.empties[1] = new;
      cls.empties[2] = new;
      `check_rand(cls, cls.empties[1].x, cls.empties[1] != cls.empties[2]);
    end
    begin
      automatic ClsEnumKey cls = new;
      cls.empties[EnumA] = new;
      cls.empties[EnumB] = new;
      `check_rand(cls, cls.empties[EnumA].x, cls.empties[EnumA] != cls.empties[EnumB]);
    end
    begin
      automatic ClsStringKey cls = new;
      cls.k1 = "abc";
      cls.k2 = "xyz";
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      `check_rand(cls, cls.empties["abc"].x, cls.empties["abc"] != cls.empties["xyz"]);
    end
    begin
      automatic ClsIntMember cls = new;
      `check_rand(cls, cls.empties[5].x, cls.empties[5].x > 0);
    end
    begin
      automatic ClsByteMember cls = new;
      `check_rand(cls, cls.empties[8'h12].x, cls.empties[8'h12].x > 0);
    end
    begin
      automatic ClsStringMember cls = new;
      `check_rand(cls, cls.empties["abc"].x, cls.empties["abc"].x > 0);
    end
    begin
      automatic ClsStringExprKey cls = new;
      `check_rand(cls, cls.empties["xyz"].x, cls.empties["xyz"].x > 0);
    end
    begin
      automatic ClsIntArrExprKey cls = new;
      `check_rand(cls, cls.vals["xyz"], cls.vals["xyz"] > 5 && cls.vals["abc"] > 7);
    end
    begin
      automatic ClsNestedMember cls = new;
      `check_rand(cls, cls.holder.empties["abc"].x, cls.holder.empties["abc"].x > 0);
    end
    begin
      automatic ClsIntArr cls = new;
      `check_rand(cls, cls.vals["abc"], cls.vals["abc"] > 0);
    end
    begin
      automatic ClsState cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      ok = cls.randomize(null);
      `checkd(ok, 1);
      `checkd(cls.empties["abc"] == cls.empties["xyz"], 0);
    end
    begin
      automatic ClsState cls = new;
      automatic Empty e = new;
      cls.empties["abc"] = e;
      cls.empties["xyz"] = e;
      ok = cls.randomize(null);
      `checkd(ok, 0);
      `checkd(cls.empties["abc"] == cls.empties["xyz"], 1);
    end
    begin
      automatic ClsState cls = new;
      automatic Empty e = new;
      cls.empties["abc"] = e;
      cls.empties["xyz"] = e;
      cls.constraint_mode(0);
      ok = cls.randomize(null);
      `checkd(ok, 1);
    end
    begin
      automatic NoState ns = new;
      ok = ns.randomize();
      `checkd(ok, 1);
      ok = ns.randomize(null);
      `checkd(ok, 1);
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
