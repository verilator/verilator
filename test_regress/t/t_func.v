// $Id$
// DESCRIPTION: Verilator: Verilog Test module
//
// This file ONLY is placed into the Public Domain, for any use,
// without warranty, 2003 by Wilson Snyder.

module t;
   reg [2:0] value;
   reg [31:0] global;

   initial begin
      global = 1;
      value = 2;
      if (add(value) != 3'd3) $stop;
      if (global != 2) $stop;
      if (add(add(3'd1)) != 3'd3) $stop;
      if (global != 4) $stop;
      if (munge4(4'b0010) != 4'b1011) $stop;
      if (global != 5) $stop;
      setit;
      incr(global,global,32'h10);
      if (global != 32'h17) $stop;
      nop(32'h11);

      global = 32'h00000001;
      flipupperbit(global,4'd4);
      flipupperbit(global,4'd12);
      if (global !== 32'h10100001) $stop;

      $write("*-* All Finished *-*\n");
      $finish;
   end

   function [2:0] add;
      input [2:0] from;
      begin
	 add = from + 3'd1;
	 begin : named
	    reg [31:0] flocal;
	    flocal = 1;
	    global = global + flocal;
	 end
      end
   endfunction

   function [3:0] munge4;
      input [3:0] from;		// Different from the 'from' signal above
      reg one;
      begin : named
	 reg [1:0] flocal;
	 // Function calling a function
	 one = 1'b1;
	 munge4 = {one, add(from[2:0])};
      end
   endfunction

   task setit;
      reg [31:0] temp;
      begin
	 temp = global + 32'h1;
	 global = temp + 32'h1;
      end
   endtask

   task incr;
      output [31:0] z;
      input [31:0] a;
      input [31:0] inc;
      z = a + inc;
   endtask

   task nop;
      input  [31:0] a;
      begin
      end
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

endmodule
