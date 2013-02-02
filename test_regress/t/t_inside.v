// DESCRIPTION::Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2013 by Wilson Snyder.

module t;

`define checkh(gotv,expv) do if ((gotv) !== (expv)) begin $write("%%Error: %s:%0d:  got='h%x exp='h%x\n", `__FILE__,`__LINE__, (gotv), (expv)); $stop; end while(0);

   typedef enum logic [1:0]
		{ ZERO  = 2'd0,
		  ONE   = 2'd1,
		  TWO   = 2'd2,
		  THREE = 2'd3,
		  XXX   = 2'dx
		  } num_t;

   function automatic logic is_odd;
      input 	en;
      input 	num_t number;
      case (en)
	1'b1: begin
	   unique if (number inside {ONE, THREE})
	     is_odd = 1'b1;
	   else   if (number inside {ZERO, TWO})
	     is_odd = 1'b0;
	   else
	     is_odd = 1'bx;
	end
	1'b0:    is_odd = 1'bx;
	default: is_odd = 1'bx;
      endcase
   endfunction

   initial begin
      `checkh ((4'd4 inside {4'd1,4'd5}), 1'b0);
      `checkh ((4'd4 inside {4'd1,4'd4}), 1'b1);
      //
      `checkh ((4'b1011 inside {4'b1001}), 1'b0);
      `checkh ((4'b1011 inside {4'b1xx1}), 1'b1);  // Uses ==?
      `checkh ((4'b1001 inside {4'b1xx1}), 1'b1);  // Uses ==?
      `checkh ((4'b1001 inside {4'b1??1}), 1'b1);
`ifndef VERILATOR
      `checkh ((4'b1z11 inside {4'b11?1, 4'b1011}),1'bx);
`endif
      // Range
      `checkh ((4'd4 inside {[4'd5:4'd3], [4'd10:4'd8]}), 1'b0);  // If left of colon < never matches
      `checkh ((4'd3 inside {[4'd1:4'd2], [4'd3:4'd5]}), 1'b1);
      `checkh ((4'd4 inside {[4'd1:4'd2], [4'd3:4'd5]}), 1'b1);
      `checkh ((4'd5 inside {[4'd1:4'd2], [4'd3:4'd5]}), 1'b1);
      //
      // Unsupported $ bound
      //
      // Unsupported if unpacked array, elements tranversed
      //int unpackedarray [$] = '{8,9};
      //( expr inside {2, 3, unpackedarray}) // { 2,3,8,9}
      //
      `checkh (is_odd(1'b1, ZERO), 1'd0);
      `checkh (is_odd(1'b1, ONE),  1'd1);
      `checkh (is_odd(1'b1, TWO),  1'd0);
      `checkh (is_odd(1'b1, THREE),1'd1);
`ifndef VERILATOR
      `checkh (is_odd(1'b1, XXX),  1'dx);
`endif
      //
      $write("*-* All Finished *-*\n");
      $finish;
   end
endmodule
