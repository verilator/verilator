// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t (/*AUTOARG*/
   // Outputs
   passed,
   // Inputs
   clk, fastclk, reset_l
   );

   input clk /*verilator sc_clock*/;
   input fastclk /*verilator sc_clock*/;
   input reset_l;
   output passed;

   // Combine passed signals from each sub signal
   // verilator lint_off MULTIDRIVEN
   wire [20:0] passedv;
   // verilator lint_on MULTIDRIVEN
   wire   passed = &passedv;

   assign passedv[0] = 1'b1;
   assign passedv[1] = 1'b1;
   assign passedv[2] = 1'b1;
   assign passedv[3] = 1'b1;
   assign passedv[4] = 1'b1;
   assign passedv[5] = 1'b1;
   t_inst  tinst
     (.passed		(passedv[6]),
      /*AUTOINST*/
      // Inputs
      .clk				(clk),
      .fastclk				(fastclk));
   t_param tparam
     (.passed		(passedv[7]),
      /*AUTOINST*/
      // Inputs
      .clk				(clk));
   assign passedv[8] = 1'b1;
   assign passedv[9] = 1'b1;
   assign passedv[10] = 1'b1;
   t_clk tclk
     (.passed		(passedv[11]),
      /*AUTOINST*/
      // Inputs
      .fastclk				(fastclk),
      .clk				(clk),
      .reset_l				(reset_l));
   assign passedv[12] = 1'b1;
   assign passedv[13] = 1'b1;
   t_chg tchg
     (.passed		(passedv[14]),
      /*AUTOINST*/
      // Inputs
      .clk				(clk),
      .fastclk				(fastclk));
   assign passedv[15] = 1'b1;
   assign passedv[16] = 1'b1;
   assign passedv[17] = 1'b1;
   assign passedv[18] = 1'b1;
   assign passedv[19] = 1'b1;
   t_netlist tnetlist
     (.passed		(passedv[20]),
      .also_fastclk	(fastclk),
      /*AUTOINST*/
      // Inputs
      .fastclk				(fastclk));

endmodule
