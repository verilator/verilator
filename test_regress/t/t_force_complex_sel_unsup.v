// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)
`define checkr(gotv,expv) do if ((gotv) != (expv)) begin $write("%%Error: %s:%0d:  got=%f exp=%f\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

`ifdef VERILATOR
// The '$c(1)' is there to prevent inlining of the signal by V3Gate
`define IMPURE_ONE ($c(1))
`else
// Use standard $random (chances of getting 2 consecutive zeroes is zero).
`define IMPURE_ONE (|($random | $random))
`endif

module t (  /*AUTOARG*/
    // Inputs
    clk
);
  input clk;

  integer cyc = 0;

  logic [2:0] logic_arr;

  // Test loop
  always @(posedge clk) begin
    cyc <= cyc + 1;
    if (cyc == 0) begin
      logic_arr[`IMPURE_ONE] <= 1;
    end
    else if (cyc == 1) begin
      `checkh(logic_arr[`IMPURE_ONE], 1);
    end
    else if (cyc == 2) begin
      force logic_arr[`IMPURE_ONE] = 0;
    end
    else if (cyc == 3) begin
      `checkh(logic_arr[`IMPURE_ONE], 0);
      logic_arr[`IMPURE_ONE] <= 1;
    end
    else if (cyc == 4) begin
      `checkh(logic_arr[`IMPURE_ONE], 0);
    end
    else if (cyc == 5) begin
      release logic_arr[`IMPURE_ONE];
    end
    else if (cyc == 6) begin
      `checkh(logic_arr[`IMPURE_ONE], 0);
      logic_arr[`IMPURE_ONE] <= 1;
    end
    else if (cyc == 7) begin
      `checkh(logic_arr[`IMPURE_ONE], 1);
    end
    else if (cyc == 8) begin
      $write("*-* All Finished *-*\n");
      $finish;
    end
  end
endmodule
