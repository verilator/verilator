// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

class SubClass;
  rand bit [2:0] field;
  function new ();
    field = 0;
  endfunction
endclass
class MyClass;
  SubClass sc_inst2;
  function new ();
    sc_inst2 = new;
  endfunction
endclass;
class Deep;
  MyClass sc_inst1;
  function new ();
    sc_inst1 = new;
  endfunction
endclass;
class WeNeedToGoDeeper;
  Deep sc_inst;
  function new ();
    sc_inst = new;
  endfunction
endclass;

module t;
  initial begin
    WeNeedToGoDeeper cl_inst = new;
    MyClass cl_inst2 = new;
    repeat(10) begin
      if (cl_inst.sc_inst.sc_inst1.sc_inst2.randomize() with {field inside {1, 2, 3};} == 0) begin
        $stop;
      end
      if (cl_inst.sc_inst.sc_inst1.sc_inst2.field < 1 || cl_inst.sc_inst.sc_inst1.sc_inst2.field > 3) begin
        $stop;
      end
      if (cl_inst2.sc_inst2.randomize() with {field inside {1, 2, 3};} == 0) begin
        $stop;
      end
      if (cl_inst2.sc_inst2.field < 1 || cl_inst2.sc_inst2.field > 3) begin
        $stop;
      end
    end
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule
