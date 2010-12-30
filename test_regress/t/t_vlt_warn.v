// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2010 by Wilson Snyder.

// Try inline config
`ifdef verilator
  `verilator_config
    lint_off -msg CASEX -file "t/t_vlt_warn.v"
  `verilog
`endif





module t;
   reg width_warn_var_line18 = 2'b11;  // Width warning - must be line 18
   reg width_warn2_var_line19 = 2'b11;  // Width warning - must be line 19
   reg width_warn3_var_line20 = 2'b11;  // Width warning - must be line 20

   initial begin
      casex (1'b1)
	1'b0: $stop;
      endcase

      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
