// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2018 by Wilson Snyder.

// Make sure type errors aren't suppressable
// verilator lint_off WIDTH

module t(/*AUTOARG*/);

   bit bad_parent;
   sub sub
     (.bad_sub_ref(bad_parent));  // Type mismatch

endmodule

module sub(ref real bad_sub_ref);
endmodule
