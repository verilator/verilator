// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2014 by Jonathon Donaldson.

package our_pkg;
   typedef enum logic [8-1:0] {
			       ADC_IN2IN = 8'h99,
			       ADC_IMMED = 8'h88,
			       ADC_INDIR = 8'h86,
			       ADC_INIDX = 8'h97
			       } T_Opcode;
endpackage : our_pkg

module t ();
   our our ();
endmodule

module our
  import our_pkg::*;
   ();

   T_Opcode IR = ADC_IN2IN;

   initial begin
      $write ("%s (%t)\n", IR.name, $realtime);
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
