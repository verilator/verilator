// DESCRIPTION: Verilator: Verilog Test module
//
// This program is free software; you can redistribute it and/or modify it
// under the terms of either the GNU Lesser General Public License Version 3
// or the Perl Artistic License Version 2.0.
// SPDX-FileCopyrightText: 2026 Wilson Snyder
// SPDX-License-Identifier: LGPL-3.0-only OR Artistic-2.0

interface Ifc;
  task run;
  endtask
  int data = 0;
endinterface

program Prog;
  task run;
  endtask
  int data = 0;
endprogram

module Inner;
  task run;
  endtask
endmodule

module Outer;
  Inner inner();
endmodule

module t;
  Ifc ifc1();
  Prog prog1();
  Outer outer1();

  initial begin
    disable ifc1.missing_task;
    disable prog1.missing_task;
    disable outer1.inner.missing_task;
    disable ifc1.data;
    disable prog1.data;
  end
endmodule
