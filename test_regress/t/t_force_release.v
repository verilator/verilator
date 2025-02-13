// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2025 by Antmicro.
// SPDX-License-Identifier: CC0-1.0

`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0)

// Example from IEEE 1800-2023 10.6.2

module t;
  logic a, b, c, d;
  wire e;
  and and1 (e, a, b, c);

  initial begin
    $monitor("%d d=%b,e=%b", $stime, d, e);
    assign d = a & b & c;
    a = 1;
    b = 0;
    c = 1;
    `checkh(d, 0);
    `checkh(e, 0);
    #10;
    force d = (a | b | c);
    force e = (a | b | c);
    `checkh(d, 1);
    `checkh(e, 1);
    #10;
    release d;
    release e;
    // TODO support procedural continuous assignments.
    //
    // As per IEEE 1800-2023 10.6.2, value of `d` should be updated immediately
    // after release. However, Verilator treats `assign` inside an initial block
    // as procedural assign thus value update is delayed to the next procedural assign.
    //`checkh(d, 0);

    `checkh(d, 1);
    `checkh(e, 0);
    #10 $finish;
  end
endmodule
