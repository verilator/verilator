// DESCRIPTION: Verilator: Verilog Test module

module t;
   Test0 t0 (.val0('0));
   Test1 t1 (.val1('0));
   initial begin
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule

package params;
   parameter P = 7;
endpackage

module Test0 (val0);
   parameter Z = 1;
   input [Z : 0] val0;
endmodule

module Test1 (val1);
   input logic [params::P : 0] val1;	// Fully qualified parameter
endmodule
