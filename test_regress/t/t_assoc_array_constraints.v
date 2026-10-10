// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

class Empty;
  rand int x;
endclass

class ClsNe;
  rand Empty empties[string];
  constraint c { empties["abc"] != empties["xyz"]; }
endclass

class ClsEq;
  rand Empty empties[string];
  constraint c { empties["abc"] == empties["xyz"]; }
endclass

class ClsNeK;
  rand Empty empties[string];
  constraint c { empties["abc"] != empties["abc"]; }
endclass

class ClsEqK;
  rand Empty empties[string];
  constraint c { empties["abc"] == empties["abc"]; }
endclass

class ClsMixed;
  rand int y;
  rand Empty empties[string];
  constraint c { y > 5; empties["abc"] != empties["xyz"]; }
endclass

module t;
  initial begin
    begin
      automatic ClsNe cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      if (cls.randomize() != 1) $stop;
      if (cls.empties["abc"] == cls.empties["xyz"]) $stop;
    end
    begin
      automatic ClsNe cls = new;
      automatic Empty e = new;
      cls.empties["abc"] = e;
      cls.empties["xyz"] = e;
      if (cls.randomize() != 0) $stop;
    end
    begin
      automatic ClsEq cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      if (cls.randomize() != 0) $stop;
    end
    begin
      automatic ClsEq cls = new;
      automatic Empty e = new;
      cls.empties["abc"] = e;
      cls.empties["xyz"] = e;
      if (cls.randomize() != 1) $stop;
    end
    begin
      automatic ClsNeK cls = new;
      cls.empties["abc"] = new;
      if (cls.randomize() != 0) $stop;
    end
    begin
      automatic ClsEqK cls = new;
      cls.empties["abc"] = new;
      if (cls.randomize() != 1) $stop;
    end
    begin
      automatic ClsNe cls = new;
      if (cls.randomize() != 0) $stop;
      if (cls.empties.size() != 0) $stop;
    end
    begin
      automatic ClsNe cls = new;
      cls.empties["abc"] = new;
      if (cls.randomize() != 1) $stop;
      if (cls.empties.size() != 1) $stop;
    end
    begin
      automatic ClsMixed cls = new;
      cls.empties["abc"] = new;
      cls.empties["xyz"] = new;
      if (cls.randomize() != 1) $stop;
      if (cls.y <= 5) $stop;
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
