// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2005-2007 by Wilson Snyder.

module t (/*AUTOARG*/);

   reg [3:0] value;
   reg [3:0] valuex;

   // verilator lint_off CASEOVERLAP
   // verilator lint_off CASEWITHX
   // verilator lint_off CASEX

   // Note for Verilator Xs must become zeros, or the Xs may match.

   initial begin
      value  = 4'b1001;
      valuex = 4'b1xxx;
      case (value)
	4'b1xxx: $stop;
	4'b1???: $stop;
	4'b1001: ;
	default: $stop;
      endcase
      case (valuex)
	4'b1???: $stop;
	4'b1xxx: ;
	4'b1001: ;
	4'b1000: ;  // 1xxx is mapped to this by Verilator -x-assign 0
	default: $stop;
      endcase
      //
      casex (value)
	4'b100x: ;
	default: $stop;
      endcase
      casex (value)
	4'b100?: ;
	default: $stop;
      endcase
      casex (valuex)
	4'b100x: ;
	default: $stop;
      endcase
      casex (valuex)
	4'b100?: ;
	default: $stop;
      endcase
      //
      casez (value)
	4'bxxxx: $stop;
	4'b100?: ;
	default: $stop;
      endcase
      casez (valuex)
	4'b1xx?: ;
	4'b100?: ;  // 1xxx is mapped to this by Verilator -x-assign 0
	default: $stop;
      endcase
      $write("*-* All Finished *-*\n");
      $finish;
   end

endmodule
