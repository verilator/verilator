// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain.
// SPDX-FileCopyrightText: 2012 Wilson Snyder
// SPDX-License-Identifier: CC0-1.0

// verilog_format: off
`define stop $stop
`define checkd(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got=%0d exp=%0d (%s !== %s)\n", `__FILE__,`__LINE__, (gotv), (expv), `"gotv`", `"expv`"); `stop; end while(0);
// verilog_format: on

module t;

  m3 u_m3[1:0] ();
  defparam u_m3[0].PAR3 = 100;
  defparam u_m3[1].PAR3 = 200;

  m1 #(0) m1a ();
  m1 #(1) m1b ();

  generate
    for (genvar i = 0; i < 8; i = i + 1) begin : blk
      m3 u_m3 ();
      defparam blk[i].u_m3.PAR3 = i;
    end
  endgenerate

  initial begin
    `checkd(u_m3[0].PAR3, 100);
    `checkd(u_m3[1].PAR3, 200);

    `checkd(m1a.W, 0);
    `checkd(m1a.gblk.w0.m2.PAR2, 8);
    `checkd(m1a.gblk.w0.m2.m3.PAR3, 80);
    `checkd(m1b.W, 1);
    `checkd(m1b.gblk.w1.m2.PAR2, 4);
    `checkd(m1b.gblk.w1.m2.m3.PAR3, 40);
    $write("*-* All Finished *-*\n");
    $finish;
  end
endmodule

module m1 ();
  parameter W = 0;
  begin : gblk
    if (W == 0) begin : w0
      m2 m2 (.*);
      defparam m2.PAR2 = 8; defparam m2.m3.PAR3 = 80;
    end
    else begin : w1
      m2 m2 (.*);
      defparam m2.PAR2 = 4; defparam m2.m3.PAR3 = 40;
    end
  end
endmodule

module m2 ();
  parameter PAR2 = 20;
  m3 m3 (.*);
endmodule

module m3 ();
  parameter PAR3 = 40;
endmodule
