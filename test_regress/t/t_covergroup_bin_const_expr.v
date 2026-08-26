// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain
// SPDX-FileCopyrightText: 2026 Antmicro
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off

`define stop $stop
`define checkr(gotv,expv) do if ((roundTo5Dec(gotv)) !== (roundTo5Dec(expv))) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), expv); `stop; end while(0);
// verilog_format: on

function automatic real roundTo5Dec(real x);
  int ix = int'(x * 100_000);
  return ix / 100_000.0;
endfunction

`define BIN_PERCENTAGE(covered, TOTAL_BINS) ((covered / TOTAL_BINS) * 100.0)
// Values covergroup helper
`define VBIN_PERCENTAGE(covered) `BIN_PERCENTAGE(covered,7)
// Ranges covergroup helper
`define RBIN_PERCENTAGE(covered) `BIN_PERCENTAGE(covered,35)

module t #(
    parameter int PARAM = 9
) ();
  logic [5:0] val;
  localparam logic [5:0] LOCAL_PARAM = 0;
  covergroup c_trans;
    coverpoint val {
      bins bins1 = (1 + 1 => 2 + 2 => 3 + 3 => PARAM => LOCAL_PARAM);  // 2 => 4 => 6 => 9 => 0
    }
  endgroup
  covergroup c_values;
    coverpoint val {
      // 1,2,3,4,5,9,0
      bins bins2[] = {(1 & 1) ^ 0, 2 * 1, 3 * 4 / 2 / 2, 4, (5 ** 2) - 20, PARAM, LOCAL_PARAM};
    }
  endgroup
  covergroup c_ranges;
    coverpoint val {
      // 27:51 and [0:9] == 35 total bins
      bins bins3[] = {[3 ** 3 : 58 - 7], [LOCAL_PARAM : PARAM]};
    }
  endgroup
  c_trans  ctrans;
  c_values cvalues;
  c_ranges cranges;


  initial begin
    ctrans  = new();
    cvalues = new();
    cranges = new();
    // Transition
    `checkr(ctrans.get_inst_coverage(), 0.0);
    val = 2;
    ctrans.sample();
    val = 4;
    ctrans.sample();
    val = 6;
    ctrans.sample();
    val = 9;
    ctrans.sample();
    val = 0;
    ctrans.sample();
    `checkr(ctrans.get_inst_coverage(), 100.0);

    // Value array
    `checkr(cvalues.get_inst_coverage(), 0.0);
    val = 1;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(1.0));
    val = 2;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(2.0));
    val = 3;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(3.0));
    val = 4;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(4.0));
    val = 5;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(5.0));
    val = 9;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(6.0));
    val = 0;
    cvalues.sample();
    `checkr(cvalues.get_inst_coverage(), `VBIN_PERCENTAGE(7.0));

    // Ranges
    `checkr(cranges.get_inst_coverage(), 0.0);
    val = 27;
    cranges.sample();
    `checkr(cranges.get_inst_coverage(), `RBIN_PERCENTAGE(1.0));
    val = 40;
    cranges.sample();
    `checkr(cranges.get_inst_coverage(), `RBIN_PERCENTAGE(2.0));
    val = 48;
    cranges.sample();
    `checkr(cranges.get_inst_coverage(), `RBIN_PERCENTAGE(3.0));
    val = 0;
    cranges.sample();
    `checkr(cranges.get_inst_coverage(), `RBIN_PERCENTAGE(4.0));
    val = 5;
    cranges.sample();
    `checkr(cranges.get_inst_coverage(), `RBIN_PERCENTAGE(5.0));
    val = 9;
    cranges.sample();
    `checkr(cranges.get_inst_coverage(), `RBIN_PERCENTAGE(6.0));

    $finish;
  end
endmodule
