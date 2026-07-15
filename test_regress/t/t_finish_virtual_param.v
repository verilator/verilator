// DESCRIPTION: Verilator: Parameterized virtual families keep separate finish effects
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2026 Jeffrey Song
// SPDX-License-Identifier: CC0-1.0

class ParamBase #(
    bit FINISHES = 0
);
  virtual task run(ref int counter);
    if (FINISHES) $finish;
    counter++;
  endtask
endclass

class ParamDerived #(
    bit FINISHES = 0
) extends ParamBase #(FINISHES);
  virtual task run(ref int counter);
    if (FINISHES) $finish;
    counter++;
  endtask
endclass

module t;
  ParamBase #(1'b1) finish_object;
  ParamBase #(1'b0) normal_object;
  int finish_count;
  int normal_count;

  initial begin
    ParamDerived #(1'b1) finish_derived;
    ParamDerived #(1'b0) normal_derived;
    finish_derived = new;
    normal_derived = new;
    finish_object = finish_derived;
    normal_object = normal_derived;
    if ($test$plusargs("RUN_FINISH")) finish_object.run(finish_count);
    else normal_object.run(normal_count);
    if (finish_count != 0) $stop;
    if (normal_count != 1) $stop;
    $write("*-* All Finished *-*\n");
  end
endmodule
