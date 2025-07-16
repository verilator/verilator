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
typedef SubClass Sc_t;
class MyClass;
  Sc_t sc_inst2[2];
  function new ();
    sc_inst2[1] = new;
  endfunction
endclass;
typedef MyClass Mc_t;
class Deep;
  Mc_t sc_inst1;
  function new ();
    sc_inst1 = new;
  endfunction
endclass;
typedef Deep D_t;
class WeNeedToGoDeeper;
  D_t sc_inst;
  function new ();
    sc_inst = new;
  endfunction
endclass;

typedef WeNeedToGoDeeper WNTGDA_t[100];
typedef MyClass MCA_t[2];

module t;
  initial begin
    WNTGDA_t cl_inst;
    MCA_t cl_inst2;
    cl_inst[1] = new;
    cl_inst2[0] = new;
    repeat(10) begin
      if (cl_inst[1].sc_inst.sc_inst1.sc_inst2[1].randomize() with {field inside {1, 2, 3};} == 0) begin
        $stop;
      end
      if (cl_inst[1].sc_inst.sc_inst1.sc_inst2[1].field < 1 || cl_inst[1].sc_inst.sc_inst1.sc_inst2[1].field > 3) begin
        $stop;
      end
      if (cl_inst2[0].sc_inst2[1].randomize() with {field inside {1, 2, 3};} == 0) begin
        $stop;
      end
      if (cl_inst2[0].sc_inst2[1].field < 1 || cl_inst2[0].sc_inst2[1].field > 3) begin
        $stop;
      end
    end
   $write("*-* All Finished *-*\n");
   $finish;
  end
endmodule
