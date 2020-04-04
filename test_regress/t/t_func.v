// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed under the Creative Commons Public Domain, for
// any use, without warranty, 2003 by Wilson Snyder.
// SPDX-License-Identifier: CC0-1.0

module t;
   reg [2:0] value;
   reg [31:0] rglobal;
   reg [31:0] vec [1:0];
   reg [31:0] n;

   initial begin
      rglobal = 1;
      value = 2;
      if (add(value) != 3'd3) $stop;
      if (rglobal != 2) $stop;
      if (add(add(3'd1)) != 3'd3) $stop;
      if (rglobal != 4) $stop;
      if (munge4(4'b0010) != 4'b1011) $stop;
      if (toint(2) != 3) $stop;
      if (rglobal != 5) $stop;
      setit;
      incr(rglobal,rglobal,32'h10);
      if (rglobal != 32'h17) $stop;
      nop(32'h11);
      empty;
      empty();

      rglobal = 32'h00000001;
      flipupperbit(rglobal,4'd4);
      flipupperbit(rglobal,4'd12);
      if (rglobal !== 32'h10100001) $stop;

      if (nil_func(32'h12,32'h12) != 32'h24) $stop;
      nil_task(32'h012,32'h112,rglobal);
      if (rglobal !== 32'h124) $stop;

      vec[0] = 32'h333;
      vec[1] = 32'habc;
      incr(vec[1],vec[0],vec[1]);
      if (vec[0] != 32'h333) $stop;
      if (vec[1] != 32'hdef) $stop;

      // verilator lint_off SELRANGE
      incr(vec[2],vec[0],vec[2]);  // Reading/Writing past end of vector!
      // verilator lint_on SELRANGE

      n=1;
      nil();
      if (n !== 10) $stop;

      // Functions called as tasks
      // verilator lint_off IGNOREDRETURN
      rglobal = 32'h4;
      if (inc_and_return(32'h2) != 32'h6) $stop;
      if (rglobal !== 32'h6) $stop;
      rglobal = 32'h6;

      inc_and_return(32'h3);
      if (rglobal !== 32'h9) $stop;
      // verilator lint_on IGNOREDRETURN

      $write("*-* All Finished *-*\n");
      $finish;
   end

   function [2:0] add;
      input [2:0] fromv;
      begin
	 add = fromv + 3'd1;
	 begin : named
	    reg [31:0] flocal;
	    flocal = 1;
	    rglobal = rglobal + flocal;
	 end : named	// SystemVerilog end labels
      end
   endfunction

   function [3:0] munge4;
      input [3:0] fromv; // Different fromv than the 'fromv' signal above
      reg one;
      begin : named
	 reg [1:0] flocal;
	 // Function calling a function
	 one = 1'b1;
	 munge4 = {one, add(fromv[2:0])};
      end
   endfunction

   task setit;
      reg [31:0] temp;
      begin
	 temp = rglobal + 32'h1;
	 rglobal = temp + 32'h1;
      end
   endtask

   task incr (
	      // Check a V2K style input/output list
    output [31:0] z,
    input [31:0]  a, inc
	      );
      z = a + inc;
   endtask

   task nop;
      input  [31:0] a;
      begin
      end
   endtask

   task empty;
   endtask

   task flipupperbit;
      inout [31:0] vector;
      input [3:0] bitnum;
      reg [4:0]   bitnum2;
      begin
	 bitnum2 = {1'b1, bitnum};	// A little math to test constant propagation
	 vector[bitnum2] = vector[bitnum2] ^ 1'b1;
      end
   endtask

   task nil_task;
      input [31:0] a;
      input [31:0] b;
      output [31:0] q;
      // verilator no_inline_task
      q = nil_func(a, b);
   endtask

   function void nil;
      n = 10;
   endfunction

   function [31:0] nil_func;
      input [31:0] fa;
      input [31:0] fb;
      // verilator no_inline_task
      nil_func = fa + fb;
   endfunction

   function integer toint;
      input integer fa;
      toint = fa + 32'h1;
   endfunction

   function [31:0] inc_and_return;
      input [31:0] inc;
      rglobal = rglobal + inc;
      return rglobal;
   endfunction

endmodule
