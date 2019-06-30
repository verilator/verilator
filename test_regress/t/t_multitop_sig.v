// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2019 by Wilson Snyder.

module a(in, out);
   input in;
   output out;
   assign out = !in;
   sub sub ();
   initial $display("In '%m'");
endmodule

module b(in, out);
   input in;
   output out;
   assign out = in;
   sub sub ();
   initial $display("In '%m'");
endmodule

module c(uniq_in, uniq_out);
   input uniq_in;
   output uniq_out;
   assign uniq_out = !uniq_in;
   sub sub ();
   initial $display("In '%m'");
endmodule

module sub;
   initial $display("In '%m'");
endmodule
