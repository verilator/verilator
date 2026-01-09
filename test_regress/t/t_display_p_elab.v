// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checks(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
`ifdef verilator
 `define no_optimize(v) $c(v)
`else
 `define no_optimize(v) (v)
`endif
// verilog_format: on


module t;

  // $sformatf is not supported as parameter by some simulators

  parameter int I = 234;
  parameter string IS = $sformatf(">%p<", I);
  initial `checks(IS, ">234<");

  parameter real R = 1.234;
  parameter string RS = $sformatf(">%p<", R);
  initial `checks(RS, ">1.234<");

  int u[2];
  parameter int U[2] = '{5, 6};
  parameter string US = $sformatf(">%p<", U);
  initial `checks(US, ">'{'h5, 'h6}<");

`ifndef VERILATOR
  // Generally not supported by others
  parameter int Q[$] = '{1, 2};
  parameter string QS = $sformatf(">%p<", Q);
  initial `checks(QS, "x");

  // Generally not supported by others
  parameter int D[] = '{1, 2};
  parameter string DS = $sformatf(">%p<", D);
  initial `checks(DS, ">'{1, 2}<");

  parameter int A[int] = '{1: 10, 2: 20};
  parameter string AS = $sformatf(">%p<", A);
  initial `checks(AS, "x");

  typedef struct {int f, s;} s_t;
  parameter s_t S = '{f: 10, s: 20};
  parameter string SS = $sformatf(">%p<", S);
  initial `checks(SS, ">'{f:10, s:20}<");
`endif

  // Original issue
  function integer infofunc();
    $info("%p", U);
    return 0;
  endfunction
  localparam integer return_val = infofunc();

  string s;

  initial begin
    #1;
    u[0] = `no_optimize(5);
    u[1] = `no_optimize(6);
    s = $sformatf(">%p<", u);
    `checks(s, ">'{'h5, 'h6}<");

    `checks(US, ">'{'h5, 'h6}<");
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule
