// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2023 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// Test option.name syntax: both declaration-time and runtime assignment.
// Also tests runtime read/write of option.weight, option.goal,
// option.per_instance, option.comment.

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
  // as runtime-readable/writable fields on a covergroup instance.
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
    cov2.option.weight = 2;
    cov2.option.goal = 90;
    cov2.option.per_instance = 1;
    cov2.option.comment = "my covergroup";
    `checkd(cov2.option.weight,      2);
    `checkd(cov2.option.goal,        90);
    `checkd(cov2.option.per_instance, 1);
    `checks(cov2.option.comment, "my covergroup");
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
