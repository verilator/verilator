// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test option.name syntax: both declaration-time and runtime assignment.
// Also tests option.weight, option.goal, option.per_instance, option.comment
// (currently parsed/stored but not yet used by the backend).

`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);

module t;
  // verilator lint_off COVERIGN
  logic [3:0] data;

  covergroup cg();
    option.name = "decl_name";
  endgroup

  // Test option.weight, option.goal, option.per_instance, option.comment
  // Covergroup-level options (parsed but not yet used by backend)
  covergroup cg2;
    option.weight      = 2;
    option.goal        = 90;
    option.per_instance = 1;
    option.comment     = "my covergroup";
    cp: coverpoint data;
  endgroup

  // Coverpoint-level options: weight, goal, per_instance, and comment
  covergroup cg3;
    cp: coverpoint data {
      option.weight      = 2;
      option.goal        = 90;
      option.per_instance = 1;
      option.comment     = "cp comment";
      bins lo = {[0:7]};
      bins hi = {[8:15]};
    }
  endgroup

  cg  cov1;
  cg2 cov2;
  cg3 cov3;

  initial begin
    cov1 = new;
    cov1.option.name = "new_cov1_name";
    `checks(cov1.option.name, "new_cov1_name");

    cov2 = new;
    //TODO `checkd(cov2.option.weight,      2);  // not yet implemented
    //TODO `checkd(cov2.option.goal,        90);  // not yet implemented
    //TODO `checkd(cov2.option.per_instance, 1);  // not yet implemented
    //TODO `checks(cov2.option.comment, "my covergroup");  // not yet implemented
    data = 5;
    cov2.sample();

    cov3 = new;
    data = 3;
    cov3.sample();
    data = 10;
    cov3.sample();

    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
