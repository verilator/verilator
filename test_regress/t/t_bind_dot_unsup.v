// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2013 by Ed Lander.
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); `stop; end while(0);
// verilog_format: on

module t;

  bind u_a1.u_b1 mycheck #(.CHECK('h11)) u_check ();
  bind u_a1.u_b2 mycheck #(.CHECK('h12)) u_check ();
  bind u_a2.u_b1 mycheck #(.CHECK('h21)) u_check ();
  bind u_a2.u_b2 mycheck #(.CHECK('h22)) u_check ();

  moda #(.VAL('h10)) u_a1 ();
  moda #(.VAL('h20)) u_a2 ();

  initial begin
    `checkh(u_a1.u_b1.u_check.CHECK, 'h11);
    `checkh(u_a1.u_b2.u_check.CHECK, 'h12);
    `checkh(u_a2.u_b1.u_check.CHECK, 'h21);
    `checkh(u_a2.u_b2.u_check.CHECK, 'h22);
    $write("*-* All Finished *-*\n");
    $finish;
  end

endmodule

module moda;
  parameter VAL = 0;
  modb #(.VAL(VAL + 1)) u_b1 ();
  modb #(.VAL(VAL + 2)) u_b2 ();
endmodule

module modb;
  parameter VAL = 0;
endmodule

module mycheck;
  parameter CHECK = 0;
endmodule
