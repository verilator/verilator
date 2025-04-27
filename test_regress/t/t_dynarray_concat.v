// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2024 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

`ifdef VERILATOR
 `define stop $stop
`else
 `define stop
`endif
`define checkp(gotv,expv_s) do begin string gotv_s; gotv_s = $sformatf("%p", gotv); if ((gotv_s) != (expv_s)) begin $write("%%Error: %s:%0d:  got='%s' exp='%s'\n", `__FILE__,`__LINE__, (gotv_s), (expv_s)); `stop; end end while(0);

module t(/*AUTOARG*/);

   int da[][2] = '{};
   int da2[][2] = '{'{1, 2}};

   int dd[][] = '{};
   int dd1[][] = '{'{1}};
   int dd2[][] = '{'{1, 2}};

   int dq[][$] = '{};
   int dq1[][$] = '{'{1}};
   int dq2[][$] = '{'{1, 2}};

   int qa[$][2] = '{};
   int qa2[$][2] = '{'{1, 2}};

   int qd[$][] = '{};
   int qd1[$][] = '{'{1}};
   int qd2[$][] = '{'{1, 2}};

   int qq[$][$] = '{};
   int qq1[$][$] = '{'{1}};
   int qq2[$][$] = '{'{1, 2}};

   initial begin
      `checkp(da, "'{}");
      `checkp(da2, "'{'{'h1, 'h2} } ");

      `checkp(dd, "'{}");
      `checkp(dd1, "'{'{'h1} } ");
      `checkp(dd2, "'{'{'h1, 'h2} } ");

      `checkp(dq, "'{}");
      `checkp(dq1, "'{'{'h1} } ");
      `checkp(dq2, "'{'{'h1, 'h2} } ");

      `checkp(qa, "'{}");
      `checkp(qa2, "'{'{'h1, 'h2} } ");

      `checkp(qd, "'{}");
      `checkp(qd1, "'{'{'h1} } ");
      `checkp(qd2, "'{'{'h1, 'h2} } ");

      `checkp(qq, "'{}");
      `checkp(qq1, "'{'{'h1} } ");
      `checkp(qq2, "'{'{'h1, 'h2} } ");

      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
